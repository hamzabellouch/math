import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Reduce
import OAI.Analysis.FactorGeneration.FreeWords

namespace OAI

noncomputable section

namespace Generator

/-! Coordinate masks and permutations on the actual complex square-summable space.
These implement the Hilbert-space operations used in lem:length-one-convolution. -/
section
open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance] Classical.propDecidable
abbrev SquareSpace (X : Type*) := lp (fun _ : X => ℂ) 2

variable {X I : Type*}

theorem squareSpace_norm_sq (f : SquareSpace X) :
    ‖f‖ ^ 2 = ∑' x, ‖f x‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f

def coordinateMask (s : Set X) (f : SquareSpace X) : SquareSpace X :=
  ⟨s.indicator f, f.property.mono' (fun x => by
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx])⟩

@[simp] theorem coordinateMask_apply (s : Set X) (f : SquareSpace X) (x : X) :
    coordinateMask s f x = if x ∈ s then f x else 0 := rfl

theorem coordinateMask_norm_le (s : Set X) (f : SquareSpace X) :
    ‖coordinateMask s f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro x
  by_cases hx : x ∈ s <;> simp [hx]

theorem coordinateMask_add_compl (s : Set X) (f : SquareSpace X) :
    coordinateMask s f + coordinateMask sᶜ f = f := by
  ext x
  change coordinateMask s f x + coordinateMask sᶜ f x = f x
  by_cases hx : x ∈ s <;> simp [hx]

def coordinatePermute (e : X ≃ X) (f : SquareSpace X) : SquareSpace X :=
  ⟨fun x => f (e x), memℓp_gen ((e.summable_iff).2 (f.property.summable (by norm_num)))⟩

@[simp] theorem coordinatePermute_apply (e : X ≃ X) (f : SquareSpace X) (x : X) :
    coordinatePermute e f x = f (e x) := rfl

theorem coordinatePermute_norm (e : X ≃ X) (f : SquareSpace X) :
    ‖coordinatePermute e f‖ = ‖f‖ := by
  have h : ‖coordinatePermute e f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [squareSpace_norm_sq, squareSpace_norm_sq]
    exact e.tsum_eq (fun x => ‖f x‖ ^ 2)
  nlinarith [norm_nonneg (coordinatePermute e f), norm_nonneg f]

/-- Reindexing by a permutation, as a bounded complex linear operator. -/
def coordinatePermuteCLM (e : X ≃ X) : SquareSpace X →L[ℂ] SquareSpace X :=
  LinearMap.mkContinuous
    { toFun := coordinatePermute e
      map_add' := by intros; ext x; rfl
      map_smul' := by intros; ext x; rfl }
    1 (fun f => by simpa using (coordinatePermute_norm e f).le)

@[simp] theorem coordinatePermuteCLM_apply (e : X ≃ X) (f : SquareSpace X) (x : X) :
    coordinatePermuteCLM e f x = f (e x) := rfl

/-- Disjoint coordinate support implies genuine Hilbert orthogonality. -/
theorem squareSpace_inner_zero {f g : SquareSpace X}
    (h : ∀ x, f x = 0 ∨ g x = 0) : inner ℂ f g = 0 := by
  change (∑' x, inner ℂ (f x) (g x)) = 0
  have hz : ∀ x, inner ℂ (f x) (g x) = 0 := by
    intro x
    rcases h x with hx | hx <;> simp [hx]
  simp only [hz, tsum_zero]

/-- Pythagoras for a finite family with disjoint supports. -/
theorem squareSpace_sum_norm_sq (s : Finset I) (f : I → SquareSpace X)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x, f i x = 0 ∨ f j x = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hc : inner ℂ (∑ i ∈ s, f i) (∑ i ∈ s, f i) =
      ∑ i ∈ s, inner ℂ (f i) (f i) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
    exact Finset.sum_eq_single i
      (fun j hj hji => squareSpace_inner_zero (h i hi j hj hji.symm))
      (fun hn => (hn hi).elim)
  have hr := congrArg (RCLike.re : ℂ → ℝ) hc
  simpa only [map_sum, inner_self_eq_norm_sq] using hr

/-- The projections onto finitely many disjoint coordinate sets have total
squared mass at most that of the original vector. -/
theorem coordinateMask_sum_sq_le (s : Finset I) (U : I → Set X)
    (hU : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (U i) (U j))
    (f : SquareSpace X) :
    ∑ i ∈ s, ‖coordinateMask (U i) f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x,
      coordinateMask (U i) f x = 0 ∨ coordinateMask (U j) f x = 0 := by
    intro i hi j hj hij x
    by_cases hx : x ∈ U i
    · right
      have hn : x ∉ U j := fun hxj => Set.disjoint_left.mp (hU i hi j hj hij) hx hxj
      simp [hn]
    · left; simp [hx]
  rw [← squareSpace_sum_norm_sq s _ horth]
  have hnorm : ‖∑ i ∈ s, coordinateMask (U i) f‖ ≤ ‖f‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro x
    simp only [lp.coeFn_sum, Finset.sum_apply]
    by_cases hex : ∃ i ∈ s, x ∈ U i
    · obtain ⟨i, hi, hxi⟩ := hex
      rw [Finset.sum_eq_single i]
      · simp [hxi]
      · intro j hj hji
        have hn : x ∉ U j := fun hxj =>
          Set.disjoint_left.mp (hU i hi j hj hji.symm) hxi hxj
        simp [hn]
      · exact fun hn => (hn hi).elim
    · have hz : ∀ i ∈ s, coordinateMask (U i) f x = 0 := by
        intro i hi
        simp [show x ∉ U i from fun hx => hex ⟨i, hi, hx⟩]
      rw [Finset.sum_eq_zero hz, norm_zero]
      exact norm_nonneg _
  nlinarith [norm_nonneg (∑ i ∈ s, coordinateMask (U i) f), norm_nonneg f]

end

/-! Length-one convolution bounds for the left regular representation of a free group on an arbitrary basis. -/
section
open scoped BigOperators InnerProductSpace
attribute [local instance] Classical.propDecidable Classical.decEq
namespace FreeConvolution
variable {A : Type*}
abbrev Letter (A : Type*) := A × Bool

def inverseLetter (a : Letter A) : Letter A := (a.1, !a.2)
def letter (a : Letter A) : FreeGroup A := FreeGroup.mk [a]
def begins (a : Letter A) (w : FreeGroup A) : Prop := w.toWord.head? = some a

@[simp] theorem inverseLetter_inverse (a : Letter A) : inverseLetter (inverseLetter a) = a := by
  cases a; simp [inverseLetter]

theorem inverseLetter_injective : Function.Injective (inverseLetter : Letter A → Letter A) :=
  Function.Involutive.injective inverseLetter_inverse

@[simp] theorem letter_toWord (a : Letter A) : (letter a).toWord = [a] := by
  simp [letter]

@[simp] theorem letter_inverse (a : Letter A) : letter (inverseLetter a) = (letter a)⁻¹ := by
  simp [letter, FreeGroup.inv_mk, FreeGroup.invRev, inverseLetter]

@[simp] theorem letter_true (a : A) : letter (a, true) = FreeGroup.of a := rfl

theorem letter_false (a : A) : letter (a, false) = (FreeGroup.of a)⁻¹ := by
  simpa [inverseLetter] using letter_inverse (a, true)

theorem letter_injective : Function.Injective (letter : Letter A → FreeGroup A) := by
  intro a b h
  have hw := congrArg FreeGroup.toWord h
  simpa only [letter_toWord, List.singleton_inj] using hw

/-- A noncancelling left multiplication creates its signed letter as the head. -/
theorem begins_letter_mul (a : Letter A) (w : FreeGroup A)
    (h : ¬ begins (inverseLetter a) w) : begins a (letter a * w) := by
  unfold begins at *
  rw [FreeGroup.toWord_mul, letter_toWord, List.singleton_append,
    FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  cases hw : w.toWord with
  | nil => simp
  | cons b bs =>
    have hn : ¬ (a.1 = b.1 ∧ a.2 = !b.2) := by
      intro he
      apply h
      simp only [hw, List.head?_cons, Option.some.injEq]
      apply Prod.ext
      · exact he.1.symm
      · simpa [inverseLetter] using congrArg Bool.not he.2.symm
    simp [hn]

/-- The actual left regular translation λ(g)η(x)=η(g⁻¹x). -/
def leftRegular (g : FreeGroup A) : SquareSpace (FreeGroup A) →L[ℂ] SquareSpace (FreeGroup A) :=
  coordinatePermuteCLM (Equiv.mulLeft g⁻¹)

@[simp] theorem leftRegular_apply (g : FreeGroup A) (f : SquareSpace (FreeGroup A))
    (x : FreeGroup A) : leftRegular g f x = f (g⁻¹ * x) := rfl

@[simp] theorem leftRegular_norm (g : FreeGroup A) (f : SquareSpace (FreeGroup A)) :
    ‖leftRegular g f‖ = ‖f‖ := coordinatePermute_norm _ _

def creation (a : Letter A) (f : SquareSpace (FreeGroup A)) : SquareSpace (FreeGroup A) :=
  leftRegular (letter a) (coordinateMask {w | ¬ begins (inverseLetter a) w} f)

def cancellation (a : Letter A) (f : SquareSpace (FreeGroup A)) : SquareSpace (FreeGroup A) :=
  leftRegular (letter a) (coordinateMask {w | begins (inverseLetter a) w} f)

theorem creation_add_cancellation (a : Letter A) (f : SquareSpace (FreeGroup A)) :
    creation a f + cancellation a f = leftRegular (letter a) f := by
  rw [creation, cancellation, ← map_add]
  congr 1
  ext x
  change coordinateMask {w | ¬ begins (inverseLetter a) w} f x +
    coordinateMask {w | begins (inverseLetter a) w} f x = f x
  by_cases hx : begins (inverseLetter a) x <;> simp [hx]

theorem creation_support (a : Letter A) (f : SquareSpace (FreeGroup A)) (x : FreeGroup A)
    (hx : ¬ begins a x) : creation a f x = 0 := by
  simp only [creation, leftRegular_apply, coordinateMask_apply, Set.mem_ofPred_eq]
  rw [ite_eq_right]
  intro hn
  apply hx
  simpa using begins_letter_mul a ((letter a)⁻¹ * x) hn

theorem begins_disjoint {a b : Letter A} (hab : a ≠ b) :
    Disjoint {w : FreeGroup A | begins a w} {w | begins b w} := by
  apply Set.disjoint_left.mpr
  intro w ha hb
  exact hab (Option.some.inj (ha.symm.trans hb))

theorem creation_norm_le (a : Letter A) (f : SquareSpace (FreeGroup A)) :
    ‖creation a f‖ ≤ ‖f‖ := by
  rw [creation, leftRegular_norm]
  exact coordinateMask_norm_le _ _

theorem creation_sum_bound (s : Finset (Letter A)) (b : Letter A → ℂ)
    (f : SquareSpace (FreeGroup A)) :
    ‖∑ a ∈ s, b a • creation a f‖ ≤ Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) * ‖f‖ := by
  have horth : ∀ a ∈ s, ∀ c ∈ s, a ≠ c → ∀ x,
      (b a • creation a f) x = 0 ∨ (b c • creation c f) x = 0 := by
    intro a _ c _ hac x
    by_cases hx : begins a x
    · right
      have hn : ¬ begins c x := fun hc => Set.disjoint_left.mp (begins_disjoint hac) hx hc
      simp [lp.coeFn_smul, creation_support c f x hn]
    · left; simp [lp.coeFn_smul, creation_support a f x hx]
  have hsq : ‖∑ a ∈ s, b a • creation a f‖ ^ 2 ≤
      (∑ a ∈ s, ‖b a‖ ^ 2) * ‖f‖ ^ 2 := by
    rw [squareSpace_sum_norm_sq s _ horth, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    rw [norm_smul, mul_pow]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (creation_norm_le a f)
  have hS : 0 ≤ ∑ a ∈ s, ‖b a‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) * ‖f‖) ^ 2 =
      (∑ a ∈ s, ‖b a‖ ^ 2) * ‖f‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hS]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    (hsq.trans_eq he.symm)

theorem cancellation_sum_bound (s : Finset (Letter A)) (b : Letter A → ℂ)
    (f : SquareSpace (FreeGroup A)) :
    ‖∑ a ∈ s, b a • cancellation a f‖ ≤ Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) * ‖f‖ := by
  have hmass : ∑ a ∈ s, ‖cancellation a f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    simp only [cancellation, leftRegular_norm]
    exact coordinateMask_sum_sq_le s _
      (fun a _ c _ hac => begins_disjoint (fun h => hac (inverseLetter_injective h))) f
  calc
    _ ≤ ∑ a ∈ s, ‖b a‖ * ‖cancellation a f‖ := by
      simpa only [norm_smul] using norm_sum_le s (fun a => b a • cancellation a f)
    _ ≤ Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) *
        Real.sqrt (∑ a ∈ s, ‖cancellation a f‖ ^ 2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) * Real.sqrt (‖f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_sq (norm_nonneg f)]

/-- The manuscript's length-one bound on every vector of ℓ²(FreeGroup A). -/
theorem length_one_convolution_vector_bound (s : Finset (Letter A)) (b : Letter A → ℂ)
    (f : SquareSpace (FreeGroup A)) :
    ‖(∑ a ∈ s, b a • leftRegular (letter a)) f‖ ≤
      (2 * Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2)) * ‖f‖ := by
  have he : (∑ a ∈ s, b a • leftRegular (letter a)) f =
      (∑ a ∈ s, b a • creation a f) + (∑ a ∈ s, b a • cancellation a f) := by
    simp only [sum_apply, smul_apply,
      ← creation_add_cancellation, smul_add, Finset.sum_add_distrib]
  rw [he]
  have ht := norm_add_le (∑ a ∈ s, b a • creation a f) (∑ a ∈ s, b a • cancellation a f)
  have hc := creation_sum_bound s b f
  have hd := cancellation_sum_bound s b f
  linarith

/-- The length-one convolution estimate for the operator norm of the left regular action. -/
theorem length_one_convolution_operator_bound (s : Finset (Letter A)) (b : Letter A → ℂ) :
    ‖∑ a ∈ s, b a • leftRegular (letter a)‖ ≤
      2 * Real.sqrt (∑ a ∈ s, ‖b a‖ ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact length_one_convolution_vector_bound s b

end FreeConvolution

end

/-! Group-ring action on ℓ² and the coefficient-vector identity. -/
section
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable Classical.decEq
namespace FreeConvolution
variable {A : Type*}
local notation "H" => SquareSpace (FreeGroup A)
local notation "Op" => H →L[ℂ] H

def leftRegularHom : FreeGroup A →* Op where
  toFun := leftRegular
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_inv_rev, mul_assoc]

def regular : MonoidAlgebra ℂ (FreeGroup A) →ₐ[ℂ] Op :=
  MonoidAlgebra.lift ℂ Op (FreeGroup A) leftRegularHom

def realRegular : MonoidAlgebra ℝ (FreeGroup A) →ₐ[ℝ] Op :=
  MonoidAlgebra.lift ℝ Op (FreeGroup A) leftRegularHom

def delta : H := lp.single 2 1 1

@[simp] theorem delta_apply (x : FreeGroup A) : (delta : H) x = if x = 1 then 1 else 0 := by
  by_cases hx : x = 1 <;> simp [delta, lp.single_apply, hx]

@[simp] theorem delta_norm : ‖(delta : H)‖ = 1 := by
  simp [delta, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

@[simp] theorem leftRegular_delta_apply (g x : FreeGroup A) :
    leftRegular g (delta : H) x = if x = g then 1 else 0 := by
  simp [inv_mul_eq_one, eq_comm]

/-- Applying the actual convolution operator to δ₁ recovers every coefficient. -/
theorem regular_delta_apply (f : MonoidAlgebra ℂ (FreeGroup A)) (x : FreeGroup A) :
    regular f delta x = f.coeff x := by
  simp only [regular, MonoidAlgebra.lift_apply, Finsupp.sum, sum_apply, smul_apply,
    leftRegularHom]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
  simp [inv_mul_eq_one, eq_comm, Finsupp.mem_support_iff]

theorem realRegular_delta_apply (f : MonoidAlgebra ℝ (FreeGroup A)) (x : FreeGroup A) :
    realRegular f delta x = (f.coeff x : ℂ) := by
  simp only [realRegular, MonoidAlgebra.lift_apply, Finsupp.sum, sum_apply, smul_apply,
    leftRegularHom]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply]
  simp [inv_mul_eq_one, eq_comm, Finsupp.mem_support_iff]
  intro h
  simp [← h]

theorem regular_single_delta (g : FreeGroup A) :
    regular (MonoidAlgebra.single g 1) delta = lp.single 2 g 1 := by
  ext x
  rw [regular_delta_apply]
  by_cases hx : x = g <;> simp [MonoidAlgebra.coeff_single, lp.single_apply, hx]

theorem regular_delta_orthonormal :
    Orthonormal ℂ (fun g : FreeGroup A => regular (MonoidAlgebra.single g 1) delta) := by
  rw [orthonormal_iff_ite]
  intro g h
  simp only [regular_single_delta]
  by_cases hgh : g = h
  · subst h
    simp [inner_self_eq_norm_sq_to_K, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  · rw [ite_eq_right hgh]
    apply squareSpace_inner_zero
    intro x
    by_cases hx : x = g
    · right
      have hx' : x ≠ h := by simpa [hx] using hgh
      simp [lp.single_apply, hx']
    · left; simp [lp.single_apply, hx]

/-- Exact finite coefficient L² isometry in the regular representation. -/
theorem regular_coefficient_isometry (f : MonoidAlgebra ℂ (FreeGroup A)) :
    ‖regular f delta‖ ^ 2 = ∑ x ∈ f.coeff.support, ‖f.coeff x‖ ^ 2 := by
  rw [squareSpace_norm_sq]
  simp only [regular_delta_apply]
  apply tsum_eq_sum
  intro x hx
  simp [Finsupp.notMem_support_iff.mp hx]

/-- Coefficient domination implies the ℓ² inequality; no comparison between
operator norms in distinct representations is used. -/
theorem regular_delta_norm_le {f : MonoidAlgebra ℂ (FreeGroup A)}
    {a : MonoidAlgebra ℝ (FreeGroup A)} (h : ∀ x, ‖f.coeff x‖ ≤ a.coeff x) :
    ‖regular f delta‖ ≤ ‖realRegular a delta‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro x
  rw [regular_delta_apply, realRegular_delta_apply, Complex.norm_real]
  exact (h x).trans (le_abs_self _)

/-- Actual coefficient-vector power estimate. -/
theorem realRegular_pow_delta_norm_le (a : MonoidAlgebra ℝ (FreeGroup A)) (d : ℕ) :
    ‖realRegular (a ^ d) delta‖ ≤ ‖realRegular a‖ ^ d := by
  rw [map_pow]
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', pow_succ']
    exact (ContinuousLinearMap.le_opNorm (realRegular a) _).trans
      (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

end FreeConvolution

end

/-! The finite coefficient L² identity from orthonormality of reduced-word images. -/
section
open scoped BigOperators InnerProductSpace
variable {G E : Type*} [Monoid G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Linear images of a group-ring sum are its literal finite coefficient combination. -/
theorem groupRing_linear_combination (Ψ : MonoidAlgebra ℂ G →ₗ[ℂ] E)
    (f : MonoidAlgebra ℂ G) :
    Ψ f = ∑ g ∈ f.coeff.support, f.coeff g • Ψ (MonoidAlgebra.single g 1) := by
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single f]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [← map_smul]
  congr 1
  simp

/-- The source's coefficient isometry from actual orthonormal word images. -/
theorem groupRing_coefficient_isometry (Ψ : MonoidAlgebra ℂ G →ₗ[ℂ] E)
    (hΨ : Orthonormal ℂ (fun g => Ψ (MonoidAlgebra.single g 1)))
    (f : MonoidAlgebra ℂ G) :
    ‖Ψ f‖ ^ 2 = ∑ g ∈ f.coeff.support, ‖f.coeff g‖ ^ 2 := by
  rw [groupRing_linear_combination Ψ f, ← inner_self_eq_norm_sq (𝕜 := ℂ), hΨ.inner_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [mul_comm]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (f.coeff g)

/-- Two orthonormal realizations have exactly the same coefficient norm. -/
theorem groupRing_norm_eq_of_orthonormal {E' : Type*} [NormedAddCommGroup E']
    [InnerProductSpace ℂ E'] (Ψ : MonoidAlgebra ℂ G →ₗ[ℂ] E)
    (Θ : MonoidAlgebra ℂ G →ₗ[ℂ] E')
    (hΨ : Orthonormal ℂ (fun g => Ψ (MonoidAlgebra.single g 1)))
    (hΘ : Orthonormal ℂ (fun g => Θ (MonoidAlgebra.single g 1)))
    (f : MonoidAlgebra ℂ G) : ‖Ψ f‖ = ‖Θ f‖ := by
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    ((groupRing_coefficient_isometry Ψ hΨ f).trans
      (groupRing_coefficient_isometry Θ hΘ f).symm)

/-- For orthonormal word images, the finite coefficient norm agrees with the regular representation norm. -/
theorem groupRing_norm_eq_regular {A : Type*}
    (Ψ : MonoidAlgebra ℂ (FreeGroup A) →ₗ[ℂ] E)
    (hΨ : Orthonormal ℂ (fun g => Ψ (MonoidAlgebra.single g 1)))
    (f : MonoidAlgebra ℂ (FreeGroup A)) :
    ‖Ψ f‖ = ‖FreeConvolution.regular f FreeConvolution.delta‖ := by
  have h := (groupRing_coefficient_isometry Ψ hΨ f).trans
    (FreeConvolution.regular_coefficient_isometry f).symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

end

/-! Multiplicity-weighted length-one convolution bounds. -/
open scoped BigOperators
open Generator.FreeConvolution

def prefixLetterSupport (n : ℕ) : Finset (Letter (FreeGroup ℕ)) :=
  (ratioLabels n).product Finset.univ

def prefixWeight (n : ℕ) (α : ℝ) (a : Letter (FreeGroup ℕ)) : ℝ :=
  α / (2 * n) * multiplicity n a.1

/-- The exact collected multiplicities imply the required square-coefficient budget. -/
theorem prefixWeight_square_sum_le (n : ℕ) (hn : 0 < n) (α : ℝ) :
    ∑ a ∈ prefixLetterSupport n, ‖(prefixWeight n α a : ℂ)‖ ^ 2 ≤ α ^ 2 := by
  have hm : ∑ p ∈ ratioLabels n, (multiplicity n p : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ 2 := by
    have hNat : ∑ p ∈ ratioLabels n, multiplicity n p ^ 2 ≤ 2 * n ^ 2 := by
      rw [multiplicity_square_sum]
      exact Nat.sub_le _ _
    exact_mod_cast hNat
  have he : (∑ a ∈ prefixLetterSupport n, ‖(prefixWeight n α a : ℂ)‖ ^ 2) =
      2 * (α / (2 * n)) ^ 2 * ∑ p ∈ ratioLabels n, (multiplicity n p : ℝ) ^ 2 := by
    unfold prefixLetterSupport
    rw [Finset.product_eq_sprod, Finset.sum_product]
    simp only [prefixWeight, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, mul_pow]
    simp only [Fintype.sum_bool]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc
    _ ≤ 2 * (α / (2 * n)) ^ 2 * (2 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = α ^ 2 := by field_simp [hn']

/-- The manuscript's actual coefficient family has convolution norm at most 2α. -/
theorem prefix_convolution_operator_bound (n : ℕ) (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) :
    ‖∑ a ∈ prefixLetterSupport n, (prefixWeight n α a : ℂ) • leftRegular (letter a)‖ ≤
      2 * α := by
  calc
    _ ≤ 2 * Real.sqrt (∑ a ∈ prefixLetterSupport n, ‖(prefixWeight n α a : ℂ)‖ ^ 2) :=
      length_one_convolution_operator_bound _ _
    _ ≤ 2 * Real.sqrt (α ^ 2) := by
      gcongr
      exact prefixWeight_square_sum_le n hn α
    _ = _ := by rw [Real.sqrt_sq hα]

end Generator

end

end OAI

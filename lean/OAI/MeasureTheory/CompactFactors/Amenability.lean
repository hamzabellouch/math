import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

open scoped RealInnerProductSpace BoundedContinuousFunction
namespace EuclideanFiveColor.Amenable
variable (G : Type*) [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]

def shift {E : Type*} [PseudoMetricSpace E] (g : G) (f : G →ᵇ E) : G →ᵇ E :=
  f.compContinuous ⟨fun x => x + g, continuous_of_discreteTopology⟩

@[simp] lemma shift_apply {E : Type*} [PseudoMetricSpace E] (g x : G) (f : G →ᵇ E) :
    shift G g f x = f (x+g) := rfl

/-- A normalized positive translation-invariant real functional. -/
structure Mean where
  map : (G →ᵇ ℝ) →L[ℝ] ℝ
  map_const : ∀ c, map (BoundedContinuousFunction.const G c) = c
  positive : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ map f
  invariant : ∀ g f, map (shift G g f) = map f

variable {G}
namespace Mean
variable (M : Mean G)
lemma mono (f h : G →ᵇ ℝ) (hf : ∀ x, f x ≤ h x) : M.map f ≤ M.map h := by
  have hm := M.positive (h-f) (fun x => sub_nonneg.mpr (hf x))
  simpa only [map_sub, sub_nonneg] using hm

lemma abs_le (f h : G →ᵇ ℝ) (hf : ∀ x, |f x| ≤ h x) : |M.map f| ≤ M.map h := by
  rw [_root_.abs_le]
  constructor
  · have := M.mono (-h) f (fun x => (_root_.abs_le.mp (hf x)).1)
    simpa only [map_neg] using this
  · exact M.mono f h fun x => (_root_.abs_le.mp (hf x)).2

lemma exists_lt {f : G →ᵇ ℝ} {ε : ℝ} (h : M.map f < ε) : ∃ g, f g < ε := by
  by_contra hn
  push Not at hn
  have := M.mono (BoundedContinuousFunction.const G ε) f hn
  rw [M.map_const] at this
  exact (not_lt_of_ge this) h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def normFn (V : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => ‖V x‖)
    (continuous_norm.comp V.continuous) ‖V‖ (fun x => by simpa using V.norm_coe_le_norm x)
omit [AddCommGroup G] [DiscreteTopology G] [InnerProductSpace ℝ H] [CompleteSpace H] in
@[simp] lemma normFn_apply (V : G →ᵇ H) (x : G) : normFn V x = ‖V x‖ := rfl

def pairing (V : G →ᵇ H) (v : H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => inner ℝ (V x) v)
    (V.continuous.inner continuous_const) (‖V‖ * ‖v‖)
    (fun x => (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (V.norm_coe_le_norm x) (norm_nonneg v)))
omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
@[simp] lemma pairing_apply (V : G →ᵇ H) (v : H) (x : G) : pairing V v x = inner ℝ (V x) v := rfl

omit [CompleteSpace H] in
lemma pairing_bound (V : G →ᵇ H) (v : H) :
    |M.map (pairing V v)| ≤ M.map (normFn V) * ‖v‖ := by
  have he : M.map (‖v‖ • normFn V) = M.map (normFn V) * ‖v‖ := by
    rw [map_smul]; simp [mul_comm]
  rw [← he]
  apply M.abs_le
  intro x
  simpa [mul_comm] using (norm_inner_le_norm (𝕜 := ℝ) (V x) v)

def pairingMap (V : G →ᵇ H) : H →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => M.map (pairing V v)
      map_add' := by
        intro v w
        have he : pairing V (v+w) = pairing V v + pairing V w := by ext; simp [inner_add_right]
        rw [he, map_add]
      map_smul' := by
        intro c v
        have he : pairing V (c • v) = c • pairing V v := by ext; simp [inner_smul_right]
        rw [he, map_smul]; rfl }
    (M.map (normFn V)) (fun v => M.pairing_bound V v)

def vector (V : G →ᵇ H) : H := (InnerProductSpace.toDual ℝ H).symm (M.pairingMap V)

lemma vector_pair (V : G →ᵇ H) (v : H) :
    inner ℝ (M.vector V) v = M.map (pairing V v) := InnerProductSpace.toDual_symm_apply

lemma vector_norm_le (V : G →ᵇ H) : ‖M.vector V‖ ≤ M.map (normFn V) := by
  rw [vector, LinearIsometryEquiv.norm_map]
  apply (M.pairingMap V).opNorm_le_bound (M.positive _ (fun x => by simp))
  exact M.pairing_bound V

lemma vector_add (V W : G →ᵇ H) : M.vector (V+W) = M.vector V + M.vector W := by
  apply ext_inner_right ℝ; intro v
  rw [inner_add_left, M.vector_pair, M.vector_pair, M.vector_pair]
  have he : pairing (V+W) v = pairing V v + pairing W v := by ext; simp [inner_add_left]
  rw [he, map_add]

lemma vector_smul (c : ℝ) (V : G →ᵇ H) : M.vector (c • V) = c • M.vector V := by
  apply ext_inner_right ℝ; intro v
  rw [real_inner_smul_left, M.vector_pair, M.vector_pair]
  have he : pairing (c • V) v = c • pairing V v := by ext; simp [real_inner_smul_left]
  rw [he, map_smul]; rfl

lemma vector_shift (V : G →ᵇ H) (g : G) : M.vector (shift G g V) = M.vector V := by
  apply ext_inner_right ℝ; intro v
  rw [M.vector_pair, M.vector_pair]
  exact M.invariant g (pairing V v)

lemma vector_map {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [CompleteSpace J]
    (L : H →L[ℝ] J) (V : G →ᵇ H) :
    M.vector (L.compLeftContinuousBounded G V) = L (M.vector V) := by
  apply ext_inner_right ℝ; intro v
  rw [M.vector_pair, ← L.adjoint_inner_right, M.vector_pair]
  congr 1; ext x
  exact (L.adjoint_inner_right (V x) v).symm

def squareNorm (V : G →ᵇ H) : G →ᵇ ℝ := normFn V * normFn V
omit [AddCommGroup G] [DiscreteTopology G] [InnerProductSpace ℝ H] [CompleteSpace H] in
@[simp] lemma squareNorm_apply (V : G →ᵇ H) (x : G) : squareNorm V x = ‖V x‖^2 := by
  simp [squareNorm, pow_two]

lemma jensen (V : G →ᵇ H) : ‖M.vector V‖^2 ≤ M.map (squareNorm V) := by
  let c := M.vector V
  have he : squareNorm (V - BoundedContinuousFunction.const G c) =
      squareNorm V - (2 : ℝ) • pairing V c + BoundedContinuousFunction.const G (‖c‖^2) := by
    ext x
    simp only [squareNorm_apply, BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.const_apply,
      BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply, pairing_apply, smul_eq_mul]
    rw [norm_sub_sq_real]
  have hp := M.positive (squareNorm (V - BoundedContinuousFunction.const G c)) (fun x => by
    rw [squareNorm_apply]; positivity)
  rw [he, map_add, map_sub, map_smul, M.map_const, ← M.vector_pair] at hp
  change 0 ≤ M.map (squareNorm V) - 2 * inner ℝ c c + ‖c‖^2 at hp
  rw [real_inner_self_eq_norm_sq] at hp
  dsimp [c] at hp
  linarith
end Mean
end EuclideanFiveColor.Amenable

namespace EuclideanFiveColor.Amenable.Mean

section
open scoped BoundedContinuousFunction
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : Mean G)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def cross (V W : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => inner ℝ (V x) (W x))
    (V.continuous.inner W.continuous) (‖V‖ * ‖W‖) (fun x => by
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (V.norm_coe_le_norm x) (W.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)))

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
@[simp] lemma cross_apply (V W : G →ᵇ H) (x : G) : cross V W x = inner ℝ (V x) (W x) := rfl

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
lemma cross_comm (V W : G →ᵇ H) : cross V W = cross W V := by
  ext x; exact real_inner_comm _ _

omit [AddCommGroup G] [DiscreteTopology G] [CompleteSpace H] in
lemma squareNorm_add (V W : G →ᵇ H) :
    squareNorm (V+W) = squareNorm V + squareNorm W + (2 : ℝ) • cross V W := by
  ext x
  simp only [squareNorm_apply, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, cross_apply, smul_eq_mul]
  rw [norm_add_sq_real]; ring

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
lemma squareNorm_shift (V : G →ᵇ H) (g : G) :
    M.map (squareNorm (shift G g V)) = M.map (squareNorm V) :=
  M.invariant g (squareNorm V)

def correlation (V W : G →ᵇ H) : G →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun g => M.map (cross (shift G g V) W)) continuous_of_discreteTopology
    (‖V‖ * ‖W‖) (fun g => by
      rw [Real.norm_eq_abs, ← M.map_const (‖V‖ * ‖W‖)]
      apply M.abs_le
      intro x
      exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
        (mul_le_mul (V.norm_coe_le_norm (x+g)) (W.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)))

omit [CompleteSpace H] in
@[simp] lemma correlation_apply (V W : G →ᵇ H) (g : G) :
    M.correlation V W g = M.map (cross (shift G g V) W) := rfl

omit [CompleteSpace H] in
lemma correlation_add (V W Z : G →ᵇ H) :
    M.correlation V (W+Z) = M.correlation V W + M.correlation V Z := by
  ext g
  simp only [correlation_apply, BoundedContinuousFunction.add_apply]
  rw [← map_add]
  congr 1; ext x
  simp only [cross_apply, BoundedContinuousFunction.add_apply, inner_add_right]

omit [CompleteSpace H] in
lemma correlation_zero (V : G →ᵇ H) : M.correlation V 0 = 0 := by
  ext g
  change M.map (cross (shift G g V) (0 : G →ᵇ H)) = 0
  have he : cross (shift G g V) (0 : G →ᵇ H) = 0 := by ext; simp
  rw [he, map_zero]

omit [CompleteSpace H] in
lemma correlation_shift (V W : G →ᵇ H) (g : G) :
    M.correlation V (shift G g W) = shift G (-g) (M.correlation V W) := by
  ext h
  change M.map (cross (shift G h V) (shift G g W)) =
    M.map (cross (shift G (h+-g) V) W)
  rw [← M.invariant (-g) (cross (shift G h V) (shift G g W))]
  congr 1; ext x
  simp only [shift_apply, cross_apply]
  congr 2 <;> abel

/-- Invariant-mean van der Corput: positivity and finite translates suffice.
There is no exchange of iterated means. -/
theorem vector_eq_zero_of_correlation_nonpos (V : G →ᵇ H)
    (hc : M.map (M.correlation V V) ≤ 0) : M.vector V = 0 := by
  classical
  let C : ℝ := M.map (squareNorm V) + 2
  have hC : 0 < C := by
    have := M.positive (squareNorm V) (fun x => by rw [squareNorm_apply]; positivity)
    dsimp [C]; linarith
  have hW (n : ℕ) : ∃ W : G →ᵇ H, M.vector W = (n : ℝ) • M.vector V ∧
      M.map (M.correlation V W) ≤ 0 ∧ M.map (squareNorm W) ≤ (n : ℝ)*C := by
    induction n with
    | zero =>
      refine ⟨0, ?_, ?_, ?_⟩
      · have he : M.vector (0 : G →ᵇ H) = 0 := by
          apply ext_inner_right ℝ; intro v
          rw [M.vector_pair, inner_zero_left]
          have he : pairing (0 : G →ᵇ H) v = 0 := by ext; simp
          rw [he, map_zero]
        simpa using he
      · simp [M.correlation_zero]
      · have he : squareNorm (0 : G →ᵇ H) = 0 := by ext; simp
        simp [he]
    | succ n ih =>
      obtain ⟨W, hv, hwc, hwe⟩ := ih
      obtain ⟨g, hg⟩ := M.exists_lt (lt_of_le_of_lt hwc zero_lt_one)
      refine ⟨W+shift G g V, ?_, ?_, ?_⟩
      · rw [M.vector_add, M.vector_shift, hv]
        simp [Nat.cast_add, add_smul]
      · rw [M.correlation_add, map_add, M.correlation_shift, M.invariant]
        linarith
      · rw [squareNorm_add, map_add, map_add, map_smul, M.squareNorm_shift,
          cross_comm W _, ← M.correlation_apply V W g]
        have hn : ((n+1 : ℕ) : ℝ) = (n : ℝ)+1 := by simp
        rw [hn]
        dsimp [C] at *
        change M.map (squareNorm W) + M.map (squareNorm V) + 2 * M.correlation V W g ≤
          ((n : ℝ)+1) * (M.map (squareNorm V) + 2)
        change M.correlation V W g < 1 at hg
        nlinarith
  have hn (n : ℕ) (hp : 0 < n) : (n : ℝ) * ‖M.vector V‖^2 ≤ C := by
    obtain ⟨W, hw, _, he⟩ := hW n
    have hj := (M.jensen W).trans he
    rw [hw, norm_smul, Real.norm_natCast] at hj
    have hnr : 0 < (n : ℝ) := by exact_mod_cast hp
    apply (mul_le_mul_iff_right₀ hnr).mp
    nlinarith
  by_contra hv
  have hnorm : 0 < ‖M.vector V‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  obtain ⟨n, hn'⟩ := exists_nat_gt (max 0 (C / ‖M.vector V‖^2))
  have hn0 : 0 < n := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hn')
  have hratio := lt_of_le_of_lt (le_max_right _ _) hn'
  have hbad := (div_lt_iff₀ hnorm).mp hratio
  have hgood := hn n hn0
  linarith

end

open scoped BoundedContinuousFunction
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [DiscreteTopology G]
variable (M : Mean G)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def orbit (U : G → H ≃ₗᵢ[ℝ] H) (v : H) : G →ᵇ H :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => U g v)
    continuous_of_discreteTopology ‖v‖ (fun g => le_of_eq ((U g).norm_map v))

omit [AddCommGroup G] [CompleteSpace H] in
@[simp] lemma orbit_apply (U : G → H ≃ₗᵢ[ℝ] H) (v : H) (g : G) : orbit U v g = U g v := rfl

lemma vector_orbit_invariant (U : G → H ≃ₗᵢ[ℝ] H)
    (hU : ∀ g h v, U (g+h) v = U g (U h v)) (v : H) (g : G) :
    U g (M.vector (orbit U v)) = M.vector (orbit U v) := by
  change (U g).toLinearIsometry.toContinuousLinearMap (M.vector (orbit U v)) = _
  rw [← M.vector_map (U g).toLinearIsometry.toContinuousLinearMap]
  have he : (U g).toLinearIsometry.toContinuousLinearMap.compLeftContinuousBounded G (orbit U v) =
      shift G g (orbit U v) := by
    ext h
    change U g (U h v) = U (h+g) v
    rw [add_comm h g, hU]
  rw [he, M.vector_shift]

lemma vector_orbit_pair_fixed (U : G → H ≃ₗᵢ[ℝ] H) (v w : H)
    (hw : ∀ g, U g w = w) : inner ℝ (M.vector (orbit U v)) w = inner ℝ v w := by
  rw [M.vector_pair]
  have he : pairing (orbit U v) w = BoundedContinuousFunction.const G (inner ℝ v w) := by
    ext g
    change inner ℝ (U g v) w = inner ℝ v w
    calc
      inner ℝ (U g v) w = inner ℝ (U g v) (U g w) := by rw [hw g]
      _ = inner ℝ v w := (U g).inner_map_map v w
  rw [he, M.map_const]

/-- The mean ergodic projection criterion, valid for every positive invariant
mean and without an assumption that the group has a distinguished generator. -/
theorem vector_orbit_eq_zero (U : G → H ≃ₗᵢ[ℝ] H)
    (hU : ∀ g h v, U (g+h) v = U g (U h v)) (v : H)
    (hv : ∀ w, (∀ g, U g w = w) → inner ℝ v w = 0) :
    M.vector (orbit U v) = 0 := by
  have hf := M.vector_orbit_invariant U hU v
  have hi := M.vector_orbit_pair_fixed U v (M.vector (orbit U v)) hf
  rw [hv _ hf] at hi
  exact inner_self_eq_zero.mp hi

end EuclideanFiveColor.Amenable.Mean

namespace EuclideanFiveColor.Amenable.Koopman
open MeasureTheory Filter
section Action
variable {G X E : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X] (μ : Measure X)
  [VAddInvariantMeasure G X μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def linear (g : G) : Lp E 2 μ →ₗᵢ[ℝ] Lp E 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => g +ᵥ x) (measurePreserving_vadd g μ)

lemma linear_add (g h : G) (f : Lp E 2 μ) :
    linear μ (g+h) f = linear μ g (linear μ h f) := by
  change Lp.compMeasurePreserving (fun x => (g+h) +ᵥ x) _ f =
    Lp.compMeasurePreserving (fun x => g +ᵥ x) _
      (Lp.compMeasurePreserving (fun x => h +ᵥ x) _ f)
  have he : (fun x : X => (g+h) +ᵥ x) =
      (fun x => h +ᵥ x) ∘ (fun x => g +ᵥ x) := by
    funext x
    simp only [Function.comp_apply, ← add_vadd, add_comm]
  simpa only [he] using Lp.compMeasurePreserving_comp_apply f
    (measurePreserving_vadd h μ) (measurePreserving_vadd g μ)

@[simp] lemma linear_zero (f : Lp E 2 μ) : linear μ (0 : G) f = f := by
  change Lp.compMeasurePreserving (fun x => (0 : G) +ᵥ x) _ f = f
  have he : (fun x : X => (0 : G) +ᵥ x) = id := funext (fun x => zero_vadd G x)
  simpa only [he] using Lp.compMeasurePreserving_id_apply f

def action (g : G) : Lp E 2 μ ≃ₗᵢ[ℝ] Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective (linear μ g) (fun f =>
    ⟨linear μ (-g) f, by rw [← linear_add, add_neg_cancel, linear_zero]⟩)

@[simp] lemma action_apply (g : G) (f : Lp E 2 μ) : action μ g f = linear μ g f := rfl

lemma action_add (g h : G) (f : Lp E 2 μ) :
    action μ (g+h) f = action μ g (action μ h f) := linear_add μ g h f

lemma coe_action (g : G) (f : Lp E 2 μ) :
    action μ g f =ᵐ[μ] (fun x => f (g +ᵥ x)) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_vadd g μ)

end Action

variable {G X E : Type*} [AddCommGroup G] [MeasurableSpace X]
  [AddAction G X] [MeasurableConstVAdd G X] (μ : Measure X)
  [IsProbabilityMeasure μ] [ErgodicVAdd G X μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace.CountablySeparated E]

omit [IsProbabilityMeasure μ] [CompleteSpace E] in
lemma ae_eq_const_of_fixed (f : Lp E 2 μ)
    (hf : ∀ g : G, action μ g f = f) : ∃ c : E, f =ᵐ[μ] fun _ => c := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro A hA
  have := ErgodicVAdd.aeconst_of_forall_preimage_vadd_ae_eq (G := G)
    ((Lp.stronglyMeasurable f).measurable hA) (fun g => by
      have ha := coe_action μ g f
      rw [hf g] at ha
      exact ha.symm.mono (fun x hx =>
        propext (show f (g +ᵥ x) ∈ A ↔ f x ∈ A by change f (g +ᵥ x) = f x at hx; rw [hx])))
  exact eventuallyEmptyOrUniv_iff.mp this

lemma inner_fixed_zero (v : Lp E 2 μ)
    (hv : ∫ x, v x ∂μ = 0) (w : Lp E 2 μ) (hw : ∀ g : G, action μ g w = w) :
    inner ℝ v w = 0 := by
  obtain ⟨c, hc⟩ := ae_eq_const_of_fixed (G := G) μ w hw
  rw [L2.inner_def]
  calc
    (∫ x, inner ℝ (v x) (w x) ∂μ) = ∫ x, inner ℝ c (v x) ∂μ :=
      integral_congr_ae (hc.mono (fun x hx => by dsimp only at hx ⊢; rw [hx, real_inner_comm]))
    _ = inner ℝ c (∫ x, v x ∂μ) := integral_inner ((Lp.memLp v).integrable (by norm_num)) c
    _ = 0 := by rw [hv, inner_zero_right]

variable [TopologicalSpace G] [DiscreteTopology G]

theorem vector_orbit_zero (M : Mean G) (v : Lp E 2 μ)
    (hv : ∫ x, v x ∂μ = 0) : M.vector (H := Lp E 2 μ) (Mean.orbit (action (G := G) (E := E) μ) v) = 0 :=
by
  apply M.vector_orbit_eq_zero (H := Lp E 2 μ) (action (G := G) (E := E) μ)
    (action_add (G := G) (E := E) μ) v
  exact inner_fixed_zero (G := G) (E := E) μ v hv

end EuclideanFiveColor.Amenable.Koopman

end

end OAI

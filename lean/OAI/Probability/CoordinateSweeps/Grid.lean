import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps

/- A probability law on a finite sample space, with real-valued masses. -/
structure FiniteLaw (Ω : Type*) where
  mass : Ω → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ᶠ x, mass x = 1

namespace FiniteLaw

variable {Ω X Y : Type*}

instance : CoeFun (FiniteLaw Ω) (fun _ => Ω → ℝ) := ⟨FiniteLaw.mass⟩

@[ext] theorem ext {μ ν : FiniteLaw Ω} (h : ∀ x, μ x = ν x) : μ = ν := by
  cases μ
  cases ν
  congr
  exact funext h

variable [Fintype Ω] [Fintype X] [Fintype Y]

@[simp] theorem sum_mass (μ : FiniteLaw Ω) : ∑ x, μ x = 1 := by
  simpa only [finsum_eq_sum_of_fintype] using μ.total

/- Uniform probability, not counting measure. -/
def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  mass _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    rw [finsum_eq_sum_of_fintype]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

/- Push forward a law; the sample space need not map injectively. -/
def map (μ : FiniteLaw Ω) (f : Ω → X) : FiniteLaw X where
  mass y := ∑ x, if f x = y then μ x else 0
  nonneg y := Finset.sum_nonneg (fun x _ => by split_ifs; exact μ.nonneg x; exact le_rfl)
  total := by
    rw [finsum_eq_sum_of_fintype]
    classical
    rw [Finset.sum_comm]
    simp [μ.sum_mass]

@[simp] theorem uniform_apply [Nonempty Ω] (x : Ω) : uniform Ω x =
    (Fintype.card Ω : ℝ)⁻¹ := rfl

@[simp] theorem map_apply (μ : FiniteLaw Ω) (f : Ω → X) (y : X) :
    μ.map f y = ∑ x, if f x = y then μ x else 0 := rfl

/- Mixture of two laws, with the real probability range explicit. -/
def mix (μ ν : FiniteLaw Ω) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) : FiniteLaw Ω where
  mass x := (1 - z) * μ x + z * ν x
  nonneg x := add_nonneg (mul_nonneg (sub_nonneg.mpr hz') (μ.nonneg x))
    (mul_nonneg hz (ν.nonneg x))
  total := by
    rw [finsum_eq_sum_of_fintype]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, μ.sum_mass, ν.sum_mass]
    ring

/- Independent laws on finitely many (possibly different) finite spaces. -/
def independent {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, Fintype (A i)]
    (μ : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) where
  mass x := ∏ i, μ i (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (μ i).nonneg (x i))
  total := by
    rw [finsum_eq_sum_of_fintype]
    rw [← Fintype.prod_sum]
    simp only [FiniteLaw.sum_mass, Finset.prod_const_one]

/- The finite total-variation convention of the source: half the l1 distance. -/
def tv (μ ν : FiniteLaw Ω) : ℝ := (1 / 2 : ℝ) * ∑ x, |μ x - ν x|

/- Probability of an event. -/
def event (μ : FiniteLaw Ω) (s : Finset Ω) : ℝ := ∑ x ∈ s, μ x

end FiniteLaw

def lineCost (m u : ℕ) : ℝ :=
  Real.log ((m : ℝ)^u / (m.descFactorial u : ℝ))

theorem monotone_prefix_average (f : ℕ → ℝ) {u m : ℕ} (hu : u ≤ m)
    (hf : ∀ i < m, ∀ j < m, i ≤ j → f i ≤ f j) :
    (m : ℝ) * (∑ i ∈ Finset.range u, f i) ≤
      (u : ℝ) * (∑ i ∈ Finset.range m, f i) := by
  have h : (∑ i ∈ Finset.range u, ∑ j ∈ Finset.Ico u m, f i) ≤
      ∑ i ∈ Finset.range u, ∑ j ∈ Finset.Ico u m, f j := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_Ico.mp hj
    exact hf i (lt_of_lt_of_le hi' hu) j hj'.2 (le_trans (le_of_lt hi') hj'.1)
  simp only [Finset.sum_const, Nat.card_Ico, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum, Nat.cast_sub hu] at h
  have hs := Finset.sum_range_add_sum_Ico f hu
  nlinarith

theorem sum_corrections (m u : ℕ) (hu : u ≤ m) :
    (∑ j ∈ Finset.range u, (Real.log m - Real.log (m-j : ℕ))) =
       (u : ℝ) * Real.log m - Real.log (m.descFactorial u : ℝ) := by
  induction u with
  | zero => simp
  | succ u ih =>
    have hum : u ≤ m := by omega
    rw [Finset.sum_range_succ, ih hum, Nat.descFactorial_succ, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast (show m-u ≠ 0 by omega))
        (by exact_mod_cast (Nat.descFactorial_pos.mpr hum).ne')]
    push_cast
    ring

theorem lineCost_eq (m u : ℕ) (hm : 0 < m) (hu : u ≤ m) :
    lineCost m u = ∑ j ∈ Finset.range u, (Real.log m - Real.log (m-j : ℕ)) := by
  rw [lineCost, Real.log_div (by positivity)
    (by exact_mod_cast (Nat.descFactorial_pos.mpr hu).ne'), Real.log_pow,
    sum_corrections m u hu]

theorem lineCost_nonneg (m u : ℕ) (hm : 0 < m) (hu : u ≤ m) :
    0 ≤ lineCost m u := by
  rw [lineCost_eq m u hm hu]
  apply Finset.sum_nonneg
  intro j hj
  have hj' : j < m := (Finset.mem_range.mp hj).trans_le hu
  apply sub_nonneg.mpr
  apply Real.log_le_log
  · exact_mod_cast (show 0 < m-j by omega)
  · exact_mod_cast (Nat.sub_le m j)

theorem full_lineCost_le (m : ℕ) (hm : 0 < m) : lineCost m m ≤ m := by
  have hs := Stirling.le_log_factorial_stirling (Nat.ne_of_gt hm)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  rw [lineCost_eq m m hm le_rfl, sum_corrections m m le_rfl, Nat.descFactorial_self]
  linarith

theorem lineCost_le (m u : ℕ) (hm : 0 < m) (hu : u ≤ m) : lineCost m u ≤ u := by
  have hs := monotone_prefix_average (fun j => Real.log m - Real.log (m-j : ℕ)) hu
    (by
      intro i hi j hj hij
      have hlog : Real.log (m-j : ℕ) ≤ Real.log (m-i : ℕ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < m-j by omega))
          (by exact_mod_cast (Nat.sub_le_sub_left hij m))
      linarith)
  rw [← lineCost_eq m u hm hu, ← lineCost_eq m m hm le_rfl] at hs
  have hall := full_lineCost_le m hm
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  nlinarith

/- Binary positions with their actual bit-coordinate labels. -/
abbrev Cube (d : ℕ) := Fin d → Bool

/- Switches on a family of disjoint two-point fibers. -/
def pairSwitch {L : Type*} (bits : L → Bool) : Equiv.Perm (Bool × L) where
  toFun x := (Bool.xor x.1 (bits x.2), x.2)
  invFun x := (Bool.xor x.1 (bits x.2), x.2)
  left_inv x := by
    rcases x with ⟨b, l⟩
    change ((b ^^ bits l) ^^ bits l, l) = (b, l)
    cases b <;> cases bits l <;> simp
  right_inv x := by
    rcases x with ⟨b, l⟩
    change ((b ^^ bits l) ^^ bits l, l) = (b, l)
    cases b <;> cases bits l <;> simp

/- The parallel-edge switch layer in one specified bit direction. -/
def binaryLayer {d : ℕ} (j : Fin d) (bits : ({k : Fin d // k ≠ j} → Bool) → Bool) :
    Equiv.Perm (Cube d) :=
  (Equiv.funSplitAt j Bool).trans ((pairSwitch bits).trans (Equiv.funSplitAt j Bool).symm)

/- Ordered composition: coordinate 0 is visited first. -/
def orderedProduct {G : Type*} [Monoid G] {d : ℕ} (g : Fin d → G) : G :=
  (List.ofFn g).reverse.prod

/- Exactly one independent fair bit for every stage-edge. -/
abbrev BinaryChoices (d : ℕ) := ∀ j : Fin d, ({k : Fin d // k ≠ j} → Bool) → Bool

instance (d : ℕ) : Nonempty (BinaryChoices d) := ⟨fun _ _ => false⟩

/- One binary coordinate sweep, with all individual switches specified. -/
def binarySweep (d : ℕ) (bits : BinaryChoices d) : Equiv.Perm (Cube d) :=
  orderedProduct (fun j => binaryLayer j (bits j))

/- The source's B_(2^d), as the pushforward of the independent fair switches. -/
def binaryLaw (d : ℕ) : FiniteLaw (Equiv.Perm (Cube d)) :=
  (FiniteLaw.uniform (BinaryChoices d)).map (binarySweep d)

/- The line law L_m(z)=(1-z)U_m+zB_m, with m=2^d. -/
def lineLaw (d : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    FiniteLaw (Equiv.Perm (Cube d)) :=
  (FiniteLaw.uniform _).mix (binaryLaw d) z hz hz'

/- An ordered power-of-two grid. Its coordinate bounds are kept in the theorem,
not hidden in a change to the definition of the process. -/
structure Grid where
  b : ℕ
  positive : 0 < b
  bits : Fin b → ℕ

namespace Grid

def size (G : Grid) : ℕ := ∏ j, 2 ^ G.bits j

abbrev Slot (G : Grid) := ∀ j, Cube (G.bits j)

abbrev Line (G : Grid) (j : Fin G.b) := ∀ k : {k : Fin G.b // k ≠ j}, Cube (G.bits k)

abbrev Choices (G : Grid) := ∀ j, G.Line j → Equiv.Perm (Cube (G.bits j))

/- Simultaneous permutations on disjoint coordinate lines. -/
def fiberPerm {A B : Type*} (p : B → Equiv.Perm A) : Equiv.Perm (A × B) where
  toFun x := (p x.2 x.1, x.2)
  invFun x := ((p x.2).symm x.1, x.2)
  left_inv x := by simp
  right_inv x := by simp

def stage (G : Grid) (ω : G.Choices) (j : Fin G.b) : Equiv.Perm G.Slot :=
  (Equiv.piSplitAt j (fun k => Cube (G.bits k))).trans
    ((fiberPerm (ω j)).trans (Equiv.piSplitAt j (fun k => Cube (G.bits k))).symm)

/- The partial sweep at a stage boundary, including boundaries 0 and b. -/
def boundary (G : Grid) (ω : G.Choices) (t : ℕ) : Equiv.Perm G.Slot :=
  ((List.ofFn (G.stage ω)).take t).reverse.prod

def sweep (G : Grid) (ω : G.Choices) : Equiv.Perm G.Slot := G.boundary ω G.b

/- Independent line choices for a single coordinate stage. -/
def stageLaw (G : Grid) (j : Fin G.b) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    FiniteLaw (G.Line j → Equiv.Perm (Cube (G.bits j))) :=
  FiniteLaw.independent (fun _ : G.Line j => lineLaw (G.bits j) z hz hz')

/- All stage-lines randomize independently, exactly as in 03-paths:5-17. -/
def choiceLaw (G : Grid) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) : FiniteLaw G.Choices :=
  FiniteLaw.independent (fun j => G.stageLaw j z hz hz')

/- Allowed grid, with R=2^r. This is precisely m_j ∈ [R,R²] in bit coordinates. -/
def Allowed (G : Grid) (r : ℕ) : Prop := ∀ j, r ≤ G.bits j ∧ G.bits j ≤ 2 * r

/- Prescribed disjoint trajectories; disjointness is required at every boundary. -/
structure Holes (G : Grid) (h : ℕ) where
  path : Fin h → Fin (G.b + 1) → G.Slot
  disjoint : ∀ t, Function.Injective (fun i => path i t)
  coordinate_step : ∀ i (j : Fin G.b) (k : Fin G.b), k ≠ j →
    path i j.succ k = path i j.castSucc k

namespace Holes

variable {G : Grid} {h : ℕ}

def Compatible (H : G.Holes h) (ω : G.Choices) : Prop :=
  ∀ i (t : Fin (G.b + 1)), G.boundary ω t (H.path i 0) = H.path i t

def Feasible (H : G.Holes h) : Prop := ∃ ω, H.Compatible ω

/- Holes using a particular stage-line, counted before that stage. -/
def lineCount (H : G.Holes h) (j : Fin G.b) (L : G.Line j) : ℕ :=
  (Finset.univ.filter (fun i : Fin h =>
    (fun k : {k : Fin G.b // k ≠ j} => H.path i j.castSucc k) = L)).card

/- The exact falling-factorial potential C(H), with (m)_0=1. -/
def cost (H : G.Holes h) : ℝ :=
  ∑ j, ∑ L : G.Line j,
    Real.log (((2 ^ G.bits j : ℕ) : ℝ) ^ H.lineCount j L /
      ((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ))

theorem lineCount_le (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    H.lineCount j L ≤ 2 ^ G.bits j := by
  have hb : H.lineCount j L ≤ Fintype.card (Cube (G.bits j)) := by
    apply Finset.card_le_card_of_injOn (fun i => H.path i j.castSucc j)
    · intro _ _
      exact Finset.mem_univ _
    · intro i hi i' hi' he
      apply H.disjoint j.castSucc
      funext k
      by_cases hk : k = j
      · subst k
        exact he
      · have h1 := (Finset.mem_filter.mp hi).2
        have h2 := (Finset.mem_filter.mp hi').2
        exact (congrFun h1 ⟨k, hk⟩).trans (congrFun h2 ⟨k, hk⟩).symm
  simpa [Cube] using hb

theorem sum_lineCount (H : G.Holes h) (j : Fin G.b) :
    ∑ L : G.Line j, H.lineCount j L = h := by
  unfold lineCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem cost_nonneg (H : G.Holes h) : 0 ≤ H.cost := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro L _
  exact lineCost_nonneg _ _ (by positivity) (H.lineCount_le j L)

theorem cost_le (H : G.Holes h) : H.cost ≤ (G.b : ℝ) * h := by
  calc
    H.cost ≤ ∑ j, ∑ L : G.Line j, (H.lineCount j L : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro L _
      exact lineCost_le _ _ (by positivity) (H.lineCount_le j L)
    _ = (G.b : ℝ) * h := by
      simp only [← Nat.cast_sum, H.sum_lineCount]
      simp

/- Permutations of the free input sites, presented as permutations fixing the
prescribed inputs. This is the symmetric group on exactly s-h sites. -/
def stabilizer (H : G.Holes h) : Subgroup (Equiv.Perm G.Slot) where
  carrier g := ∀ i, g (H.path i 0) = H.path i 0
  one_mem' _ := rfl
  mul_mem' := by
    intro g g' hg hg' i
    change g (g' (H.path i 0)) = H.path i 0
    rw [hg' i, hg i]
  inv_mem' hg i := (Equiv.symm_apply_eq _).mpr (hg i).symm

/- One feasible reference bijection is a permitted choice of identifications
of the remaining input and output sites (02-preliminaries:5). -/
def reference (H : G.Holes h) (hf : H.Feasible) : G.Choices := hf.choose

theorem reference_compatible (H : G.Holes h) (hf : H.Feasible) :
    H.Compatible (H.reference hf) := hf.choose_spec

/- The remaining permutation relative to those identifications. -/
def residual (H : G.Holes h) (hf : H.Feasible) (ω : {ω : G.Choices // H.Compatible ω}) :
    H.stabilizer :=
  ⟨(G.sweep (H.reference hf))⁻¹ * G.sweep ω.val, by
    intro i
    change (G.sweep (H.reference hf)).symm (G.sweep ω.val (H.path i 0)) = H.path i 0
    apply (Equiv.symm_apply_eq _).mpr
    exact (ω.property i (Fin.last _)).trans ((H.reference_compatible hf i (Fin.last _)).symm)⟩

end Holes

/- Joint mass of all independent stage-line choices. -/
def choiceWeight (G : Grid) (z : ℝ) (ω : G.Choices) : ℝ :=
  ∏ j, ∏ L : G.Line j,
    ((1-z) * (Fintype.card (Equiv.Perm (Cube (G.bits j))) : ℝ)⁻¹ +
      z * binaryLaw (G.bits j) (ω j L))

@[simp] theorem choiceWeight_eq (G : Grid) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1)
    (ω : G.Choices) : G.choiceWeight z ω = G.choiceLaw z hz hz' ω := rfl

theorem choiceWeight_pos (G : Grid) {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1)
    (ω : G.Choices) : 0 < G.choiceWeight z ω := by
  apply Finset.prod_pos
  intro j _
  apply Finset.prod_pos
  intro L _
  apply add_pos_of_pos_of_nonneg
  · apply mul_pos (sub_pos.mpr hz')
    exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  · exact mul_nonneg hz ((binaryLaw (G.bits j)).nonneg (ω j L))

end Grid

namespace Grid

variable (G : Grid)

@[simp] theorem boundary_zero (ω : G.Choices) : G.boundary ω 0 = 1 := by
  simp [boundary]

theorem boundary_succ (ω : G.Choices) {t : ℕ} (ht : t < G.b) :
    G.boundary ω (t+1) = G.stage ω ⟨t,ht⟩ * G.boundary ω t := by
  unfold boundary
  rw [List.take_succ_eq_append_getElem (by simpa using ht)]
  simp [List.reverse_append]

@[simp] theorem stage_apply_same (ω : G.Choices) (j : Fin G.b) (x : G.Slot) :
    G.stage ω j x j = ω j (fun k => x k) (x j) := by
  simp [stage, fiberPerm, Equiv.piSplitAt_apply, Equiv.piSplitAt_symm_apply]

theorem stage_apply_ne (ω : G.Choices) (j k : Fin G.b) (hk : k ≠ j) (x : G.Slot) :
    G.stage ω j x k = x k := by
  simp [stage, fiberPerm, Equiv.piSplitAt_apply, Equiv.piSplitAt_symm_apply, hk]

namespace Holes
variable {G} {h : ℕ}

def StepCompatible (H : G.Holes h) (ω : G.Choices) : Prop :=
  ∀ i (j : Fin G.b), G.stage ω j (H.path i j.castSucc) = H.path i j.succ

theorem compatible_iff_step (H : G.Holes h) (ω : G.Choices) :
    H.Compatible ω ↔ H.StepCompatible ω := by
  constructor
  · intro hω i j
    have hs := congrArg (fun g : Equiv.Perm G.Slot => g (H.path i 0))
      (G.boundary_succ ω j.isLt)
    change G.boundary ω (j.val+1) (H.path i 0) =
      G.stage ω j (G.boundary ω j.val (H.path i 0)) at hs
    have h1 := hω i j.succ
    have h0 := hω i j.castSucc
    simp only [Fin.val_succ, Fin.val_castSucc] at h1 h0
    rw [h1, h0] at hs
    exact hs.symm
  · intro hω i t
    have hb : ∀ n (hn : n ≤ G.b), G.boundary ω n (H.path i 0) =
        H.path i ⟨n, by omega⟩ := by
      intro n
      induction n with
      | zero => intro hn; simp
      | succ n ih =>
        intro hn
        have hnb : n < G.b := by omega
        rw [G.boundary_succ ω hnb]
        change G.stage ω ⟨n,hnb⟩ (G.boundary ω n (H.path i 0)) = _
        rw [ih (by omega)]
        exact hω i ⟨n,hnb⟩
    exact hb t.val (by omega)

/- Compatibility is a product of independent line assignment events. -/
theorem step_iff_coordinate (H : G.Holes h) (ω : G.Choices) :
    H.StepCompatible ω ↔ ∀ i (j : Fin G.b),
      ω j (fun k => H.path i j.castSucc k) (H.path i j.castSucc j) = H.path i j.succ j := by
  constructor
  · intro hω i j
    have hh := congrFun (hω i j) j
    simpa using hh
  · intro hω i j
    funext k
    by_cases hk : k = j
    · subst k
      exact (G.stage_apply_same ω j _).trans (hω i j)
    · exact (G.stage_apply_ne ω j k hk _).trans (H.coordinate_step i j k hk).symm

def OnLine (H : G.Holes h) (j : Fin G.b) (L : G.Line j) (i : Fin h) : Prop :=
  (fun k : {k : Fin G.b // k ≠ j} => H.path i j.castSucc k) = L

theorem line_input_injective (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Function.Injective (fun i : {i : Fin h // H.OnLine j L i} => H.path i j.castSucc j) := by
  intro i i' he
  apply Subtype.ext
  apply H.disjoint j.castSucc
  funext k
  by_cases hk : k = j
  · subst k; exact he
  · exact (congrFun i.property ⟨k,hk⟩).trans (congrFun i'.property ⟨k,hk⟩).symm

theorem line_output_injective (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Function.Injective (fun i : {i : Fin h // H.OnLine j L i} => H.path i j.succ j) := by
  intro i i' he
  apply Subtype.ext
  apply H.disjoint j.succ
  funext k
  by_cases hk : k = j
  · subst k; exact he
  · change H.path i.val j.succ k = H.path i'.val j.succ k
    rw [H.coordinate_step _ _ _ hk, H.coordinate_step _ _ _ hk]
    exact (congrFun i.property ⟨k,hk⟩).trans (congrFun i'.property ⟨k,hk⟩).symm

/- Disjoint source trajectories really are feasible; no probability event
is postulated to be nonempty. The main target still retains its explicit
feasibility hypothesis. -/
theorem feasible_of_disjoint (H : G.Holes h) : H.Feasible := by
  have hex : ∀ (j : Fin G.b) (L : G.Line j), ∃ σ : Equiv.Perm (Cube (G.bits j)),
      ∀ i : {i : Fin h // H.OnLine j L i}, σ (H.path i j.castSucc j) = H.path i j.succ j := by
    intro j L
    exact Equiv.Perm.exists_extending_pair _ _ (H.line_input_injective j L)
      (H.line_output_injective j L)
  choose ω hω using hex
  refine ⟨ω, (H.compatible_iff_step ω).mpr ((H.step_iff_coordinate ω).mpr ?_)⟩
  intro i j
  exact hω j (fun k => H.path i j.castSucc k) ⟨i, rfl⟩

end Holes
end Grid

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem mass_le_one (μ : FiniteLaw Ω) (x : Ω) : μ x ≤ 1 := by
  rw [← μ.sum_mass]
  exact Finset.single_le_sum (fun y _ => μ.nonneg y) (Finset.mem_univ x)

/- A uniform, finite-alphabet perturbation interval, depending on the line
size only. This proves the source's half-to-two measure comparison. -/
theorem mix_uniform_between [Nonempty Ω] (ν : FiniteLaw Ω) {z : ℝ}
    (hz : 0 ≤ z) (hzhalf : z ≤ 1/2) (hzcard : z ≤ (Fintype.card Ω : ℝ)⁻¹)
    (x : Ω) :
    (1/2 : ℝ) * uniform Ω x ≤ (uniform Ω).mix ν z hz (by linarith) x ∧
      (uniform Ω).mix ν z hz (by linarith) x ≤ 2 * uniform Ω x := by
  have hn := ν.nonneg x
  have hle := ν.mass_le_one x
  have hU : 0 ≤ uniform Ω x := (uniform Ω).nonneg x
  change (1/2 : ℝ) * uniform Ω x ≤ (1-z) * uniform Ω x + z * ν x ∧
    (1-z) * uniform Ω x + z * ν x ≤ 2 * uniform Ω x
  constructor
  · nlinarith [mul_nonneg hz hn, mul_nonneg (sub_nonneg.mpr hzhalf) hU]
  · change z ≤ uniform Ω x at hzcard
    nlinarith [mul_nonneg hz hU, mul_le_mul_of_nonneg_left hle hz]

variable [DecidableEq Ω]

def assignments {h : ℕ} (μ : FiniteLaw (Equiv.Perm Ω))
    (x y : Fin h ↪ Ω) : ℝ :=
  ∑ g : Equiv.Perm Ω, if x.trans g.toEmbedding = y then μ g else 0

theorem assignments_nonneg {h : ℕ} (μ : FiniteLaw (Equiv.Perm Ω))
    (x y : Fin h ↪ Ω) : 0 ≤ μ.assignments x y := by
  apply Finset.sum_nonneg
  intro g _
  split_ifs
  · exact μ.nonneg g
  · rfl

theorem sum_assignments {h : ℕ} (μ : FiniteLaw (Equiv.Perm Ω))
    (x : Fin h ↪ Ω) : ∑ y, μ.assignments x y = 1 := by
  unfold assignments
  rw [Finset.sum_comm]
  simp

theorem uniform_assignments_same {h : ℕ} (x y z : Fin h ↪ Ω) :
    (uniform (Equiv.Perm Ω)).assignments x y =
      (uniform (Equiv.Perm Ω)).assignments x z := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair y z y.injective z.injective
  have hz : y.trans σ.toEmbedding = z := by
    ext i
    exact hσ i
  unfold assignments
  rw [← Equiv.sum_comp (Equiv.mulLeft σ)
    (fun g : Equiv.Perm Ω => if x.trans g.toEmbedding = z then
      uniform (Equiv.Perm Ω) g else 0)]
  apply Finset.sum_congr rfl
  intro g _
  have he : x.trans (σ * g).toEmbedding = z ↔ x.trans g.toEmbedding = y := by
    rw [← hz]
    constructor
    · intro he
      ext i
      exact σ.injective (congrArg (fun f : Fin h ↪ Ω => f i) he)
    · intro he
      ext i
      change σ (g (x i)) = σ (y i)
      exact congrArg σ (congrArg (fun f : Fin h ↪ Ω => f i) he)
  simp only [Equiv.coe_mulLeft, he, uniform_apply]

theorem uniform_assignments {h : ℕ} (x y : Fin h ↪ Ω) :
    (uniform (Equiv.Perm Ω)).assignments x y =
      ((Fintype.card Ω).descFactorial h : ℝ)⁻¹ := by
  let : Nonempty (Fin h ↪ Ω) := ⟨y⟩
  have hh : (∑ z : Fin h ↪ Ω, (uniform (Equiv.Perm Ω)).assignments x y) = 1 := by
    convert sum_assignments (uniform (Equiv.Perm Ω)) x using 1
    apply Finset.sum_congr rfl
    intro z _
    exact uniform_assignments_same x y z
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_embedding_eq, Fintype.card_fin] at hh
  have hm : ((Fintype.card Ω).descFactorial h : ℝ) ≠ 0 := by
    intro hm
    rw [hm, zero_mul] at hh
    norm_num at hh
  exact ((mul_eq_one_iff_inv_eq₀ hm).mp hh).symm

theorem uniform_assignments_pos {h : ℕ} (x y : Fin h ↪ Ω) :
    0 < (uniform (Equiv.Perm Ω)).assignments x y := by
  rw [uniform_assignments]
  apply inv_pos.mpr
  exact_mod_cast Nat.descFactorial_pos.mpr (by simpa using Fintype.card_le_of_embedding x)

theorem assignments_le {h : ℕ} (μ ν : FiniteLaw (Equiv.Perm Ω)) (C : ℝ)
    (hb : ∀ g, μ g ≤ C * ν g) (x y : Fin h ↪ Ω) :
    μ.assignments x y ≤ C * ν.assignments x y := by
  unfold assignments
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _
  split_ifs
  · exact hb g
  · simp

theorem le_assignments {h : ℕ} (μ ν : FiniteLaw (Equiv.Perm Ω)) (C : ℝ)
    (hb : ∀ g, C * ν g ≤ μ g) (x y : Fin h ↪ Ω) :
    C * ν.assignments x y ≤ μ.assignments x y := by
  unfold assignments
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _
  split_ifs
  · exact hb g
  · simp

/- The exact factor four in the line-conditioning argument, with all
line assignments represented by actual injections, not abstract events. -/
theorem assignments_ratio_le_four {h v : ℕ} (μ : FiniteLaw (Equiv.Perm Ω))
    (hμlo : ∀ g, (1/2 : ℝ) * uniform (Equiv.Perm Ω) g ≤ μ g)
    (hμhi : ∀ g, μ g ≤ 2 * uniform (Equiv.Perm Ω) g)
    (x y : Fin h ↪ Ω) (x' y' : Fin (h+v) ↪ Ω) :
    μ.assignments x' y' / μ.assignments x y ≤
      4 * (((Fintype.card Ω - h).descFactorial v : ℝ)⁻¹) := by
  have hlo := le_assignments μ (uniform _) (1/2) hμlo x y
  have hhi := assignments_le μ (uniform _) 2 hμhi x' y'
  have hp := uniform_assignments_pos x y
  have hmp : 0 < μ.assignments x y := lt_of_lt_of_le (by positivity) hlo
  have hcard : h+v ≤ Fintype.card Ω := by simpa using Fintype.card_le_of_embedding x'
  have hprod : (Fintype.card Ω).descFactorial (h+v) =
      (Fintype.card Ω).descFactorial h * (Fintype.card Ω-h).descFactorial v := by
    simpa only [Nat.add_sub_cancel_left, mul_comm] using
      (Nat.descFactorial_mul_descFactorial (n := Fintype.card Ω) (k := h) (m := h+v) (by omega)).symm
  have hh : ((Fintype.card Ω).descFactorial h : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega)).ne'
  have hv : ((Fintype.card Ω-h).descFactorial v : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega)).ne'
  calc
    _ ≤ (2 * (uniform (Equiv.Perm Ω)).assignments x' y') /
          ((1/2) * (uniform (Equiv.Perm Ω)).assignments x y) := by
      exact div_le_div₀ (mul_nonneg (by norm_num) ((uniform _).assignments_nonneg x' y')) hhi (by positivity) hlo
    _ = _ := by
      rw [uniform_assignments, uniform_assignments, hprod, Nat.cast_mul]
      field_simp
      ring

end FiniteLaw

namespace Grid.Holes
variable {G : Grid} {h : ℕ}

def LineCompatible (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (σ : Equiv.Perm (Cube (G.bits j))) : Prop :=
  ∀ i : {i : Fin h // H.OnLine j L i}, σ (H.path i j.castSucc j) = H.path i j.succ j

theorem compatible_iff_lines (H : G.Holes h) (ω : G.Choices) :
    H.Compatible ω ↔ ∀ j L, H.LineCompatible j L (ω j L) := by
  rw [H.compatible_iff_step, H.step_iff_coordinate]
  constructor
  · intro hω j L i
    have hh := hω i.val j
    rw [i.property] at hh
    exact hh
  · intro hω i j
    exact hω j (fun k => H.path i j.castSucc k) ⟨i,rfl⟩

def compatibleEquiv (H : G.Holes h) :
    {ω : G.Choices // H.Compatible ω} ≃
      (∀ j L, {σ : Equiv.Perm (Cube (G.bits j)) // H.LineCompatible j L σ}) where
  toFun ω j L := ⟨ω.val j L, (H.compatible_iff_lines ω.val).mp ω.property j L⟩
  invFun σ := ⟨(fun j L => (σ j L).val),
    (H.compatible_iff_lines _).mpr (fun j L => (σ j L).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- Probability of the prescribed trajectory event, with the root definition. -/
def probability (H : G.Holes h) (z : ℝ) : ℝ :=
  ∑ ω : {ω : G.Choices // H.Compatible ω}, G.choiceWeight z ω.val

/- Exact path probability factors into its independent constrained lines. -/
theorem probability_prod (H : G.Holes h) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    H.probability z = ∏ j, ∏ L, ∑ σ : {σ // H.LineCompatible j L σ},
      lineLaw (G.bits j) z hz hz' σ.val := by
  unfold probability
  rw [← Equiv.sum_comp H.compatibleEquiv.symm]
  change (∑ σ : (∀ j L, {σ // H.LineCompatible j L σ}),
    ∏ j, ∏ L, lineLaw (G.bits j) z hz hz' (σ j L).val) = _
  rw [← Fintype.prod_sum (fun j : Fin G.b =>
    fun σ : (∀ L, {σ // H.LineCompatible j L σ}) =>
      ∏ L, lineLaw (G.bits j) z hz hz' (σ L).val)]
  apply Finset.prod_congr rfl
  intro j _
  exact (Fintype.prod_sum (fun L => fun σ : {σ // H.LineCompatible j L σ} =>
    lineLaw (G.bits j) z hz hz' σ.val)).symm

theorem card_onLine (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Fintype.card {i : Fin h // H.OnLine j L i} = H.lineCount j L := by
  have hh := Fintype.card_subtype (H.OnLine j L)
  unfold lineCount
  convert hh using 1
  congr 2

def lineCards (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Fin (H.lineCount j L) ≃ {i : Fin h // H.OnLine j L i} :=
  (Fintype.equivFinOfCardEq (H.card_onLine j L)).symm

def lineInput (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Fin (H.lineCount j L) ↪ Cube (G.bits j) :=
  H.lineCards j L |>.toEmbedding |>.trans ⟨_, H.line_input_injective j L⟩

def lineOutput (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    Fin (H.lineCount j L) ↪ Cube (G.bits j) :=
  H.lineCards j L |>.toEmbedding |>.trans ⟨_, H.line_output_injective j L⟩

theorem lineCompatible_iff_assignments (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (σ : Equiv.Perm (Cube (G.bits j))) :
    H.LineCompatible j L σ ↔ (H.lineInput j L).trans σ.toEmbedding = H.lineOutput j L := by
  constructor
  · intro hs
    apply Function.Embedding.ext
    intro i
    exact hs (H.lineCards j L i)
  · intro hs i
    obtain ⟨k,rfl⟩ := (H.lineCards j L).surjective i
    exact congrArg (fun f : Fin (H.lineCount j L) ↪ Cube (G.bits j) => f k) hs

theorem sum_subtype_eq_sum_ite_of_iff {Ω : Type*} [Fintype Ω]
    {p q : Ω → Prop} [Fintype {a // p a}] [DecidablePred q]
    (h : ∀ a, p a ↔ q a) (f : Ω → ℝ) :
    (∑ a : {a // p a}, f a.val) = ∑ a, if q a then f a else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  simp only [h a]

theorem lineProbability_eq (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    (∑ σ : {σ // H.LineCompatible j L σ}, μ σ.val) =
      μ.assignments (H.lineInput j L) (H.lineOutput j L) := by
  exact sum_subtype_eq_sum_ite_of_iff (H.lineCompatible_iff_assignments j L) μ.mass

theorem probability_eq_assignments (H : G.Holes h) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    H.probability z = ∏ j, ∏ L,
      (lineLaw (G.bits j) z hz hz').assignments (H.lineInput j L) (H.lineOutput j L) := by
  rw [H.probability_prod hz hz']
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro L _
  exact H.lineProbability_eq j L (lineLaw (G.bits j) z hz hz')

/- Under uniform line randomization each prescribed injection pays exactly
one falling-factorial denominator. -/
theorem probability_zero (H : G.Holes h) :
    H.probability 0 = ∏ j, ∏ L,
      (((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ)⁻¹) := by
  rw [H.probability_eq_assignments (le_refl 0) zero_le_one]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro L _
  have he : lineLaw (G.bits j) 0 (le_refl 0) zero_le_one = FiniteLaw.uniform _ := by
    ext σ
    simp [lineLaw, FiniteLaw.mix]
  rw [he]
  have hu := FiniteLaw.uniform_assignments (H.lineInput j L) (H.lineOutput j L)
  have hc : Fintype.card (Cube (G.bits j)) = 2 ^ G.bits j := by simp [Cube]
  rw [hc] at hu
  exact hu

end Grid.Holes
end CoordinateSweeps

end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI

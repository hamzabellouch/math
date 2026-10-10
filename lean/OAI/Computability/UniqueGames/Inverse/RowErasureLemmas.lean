import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators

noncomputable section

def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

@[simp] theorem indicator_true : indicator True = 1 := by simp [indicator]
@[simp] theorem indicator_false : indicator False = 0 := by simp [indicator]

theorem indicator_nonneg (p : Prop) : 0 ≤ indicator p := by
  classical
  unfold indicator
  split <;> norm_num

theorem indicator_le_one (p : Prop) : indicator p ≤ 1 := by
  classical
  unfold indicator
  split <;> norm_num

def uniformMass {X : Type*} [Fintype X] (p : X → Prop) : ℝ :=
  Finset.univ.expect fun x => indicator (p x)

theorem uniformMass_nonneg {X : Type*} [Fintype X] (p : X → Prop) :
    0 ≤ uniformMass p :=
  Finset.expect_nonneg fun x _ => indicator_nonneg (p x)

theorem uniformMass_le_one {X : Type*} [Fintype X] [Nonempty X]
    (p : X → Prop) : uniformMass p ≤ 1 :=
  Finset.expect_le Finset.univ_nonempty fun x _ => indicator_le_one (p x)

/-- One independent replacement value per matrix entry, not per row fiber. -/
def replaceOn {X Y : Type*} (B : X → Prop) (f replacement : X → Y) : X → Y := by
  classical
  exact fun x => if B x then replacement x else f x

theorem replaceOn_of_not_mem {X Y : Type*} (B : X → Prop)
    (f replacement : X → Y) {x : X} (hx : ¬ B x) :
    replaceOn B f replacement x = f x := by
  simp [replaceOn, hx]

theorem replaceOn_of_mem {X Y : Type*} (B : X → Prop)
    (f replacement : X → Y) {x : X} (hx : B x) :
    replaceOn B f replacement x = replacement x := by
  simp [replaceOn, hx]

def equalityAcceptance {X Y E : Type*} [Fintype E]
    (left right : E → X) (f : X → Y) : ℝ :=
  uniformMass fun e => f (left e) = f (right e)

/-- Deterministic acceptance loss under editing a set of entries. Both endpoint
marginals must equal the matrix-uniform law; no independence of endpoints is
required. This applies to every choice of replacement values. -/
theorem acceptance_le_modified_add_two_mass
    {X Y E : Type*} [Fintype X] [Fintype E]
    (left right : E → X) (B : X → Prop) (f g : X → Y)
    (unchanged : ∀ x, ¬ B x → f x = g x)
    (left_uniform : uniformMass (fun e => B (left e)) = uniformMass B)
    (right_uniform : uniformMass (fun e => B (right e)) = uniformMass B) :
    equalityAcceptance left right f ≤
      equalityAcceptance left right g + 2 * uniformMass B := by
  classical
  have pointwise : ∀ e : E,
      indicator (f (left e) = f (right e)) ≤
        indicator (g (left e) = g (right e)) +
          indicator (B (left e)) + indicator (B (right e)) := by
    intro e
    by_cases hl : B (left e)
    · have h₁ := indicator_le_one (f (left e) = f (right e))
      have h₂ := indicator_nonneg (g (left e) = g (right e))
      have h₃ := indicator_nonneg (B (right e))
      simp only [indicator, ite_eq_left hl] at *
      linarith
    · by_cases hr : B (right e)
      · have h₁ := indicator_le_one (f (left e) = f (right e))
        have h₂ := indicator_nonneg (g (left e) = g (right e))
        simp only [indicator, ite_eq_right hl, ite_eq_left hr] at *
        linarith
      · rw [unchanged _ hl, unchanged _ hr]
        simp [indicator, hl, hr]
  have h := Finset.expect_le_expect (s := Finset.univ) (fun e _ => pointwise e)
  simp only [Finset.expect_add_distrib] at h
  change equalityAcceptance left right f ≤
    equalityAcceptance left right g + uniformMass (fun e => B (left e)) +
      uniformMass (fun e => B (right e)) at h
  rw [left_uniform, right_uniform] at h
  linarith

theorem acceptance_ge_original_sub_two_mass
    {X Y E : Type*} [Fintype X] [Fintype E]
    (left right : E → X) (B : X → Prop) (f replacement : X → Y)
    (left_uniform : uniformMass (fun e => B (left e)) = uniformMass B)
    (right_uniform : uniformMass (fun e => B (right e)) = uniformMass B) :
    equalityAcceptance left right f - 2 * uniformMass B ≤
      equalityAcceptance left right (replaceOn B f replacement) := by
  have h := acceptance_le_modified_add_two_mass left right B f
    (replaceOn B f replacement)
    (fun x hx => (replaceOn_of_not_mem B f replacement hx).symm)
    left_uniform right_uniform
  linarith

/-- A matrix belongs to the erased union exactly when at least one row map
provides good advice there. -/
def goodUnion {A X : Type*} (good : A → X → Prop) (x : X) : Prop :=
  ∃ a, good a x

/-- Sample a uniform matrix, then an independent uniform row map. -/
def adviceMass {A X : Type*} [Fintype A] [Fintype X]
    (good : A → X → Prop) : ℝ :=
  Finset.univ.expect fun x => uniformMass fun a => good a x

theorem adviceMass_nonneg {A X : Type*} [Fintype A] [Fintype X]
    (good : A → X → Prop) : 0 ≤ adviceMass good :=
  Finset.expect_nonneg fun x _ => uniformMass_nonneg (fun a => good a x)

/-- Each matrix in the union has at least one successful row-map atom. No
disjointness between good fibers is needed. -/
theorem union_mass_le_card_mul_adviceMass
    {A X : Type*} [Fintype A] [Fintype X] (good : A → X → Prop) :
    uniformMass (goodUnion good) ≤ (Fintype.card A : ℝ) * adviceMass good := by
  classical
  have pointwise : ∀ x : X, indicator (goodUnion good x) ≤
      (Fintype.card A : ℝ) * uniformMass (fun a => good a x) := by
    intro x
    rw [uniformMass, Fintype.card_mul_expect]
    by_cases hx : goodUnion good x
    · obtain ⟨a, ha⟩ := hx
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset A)) (f := fun a => indicator (good a x))
        (fun a _ => indicator_nonneg (good a x)) (Finset.mem_univ a)
      simpa [indicator, ha, goodUnion, show ∃ a, good a x from ⟨a, ha⟩] using h
    · simp only [indicator, ite_eq_right hx]
      exact Finset.sum_nonneg fun a _ => indicator_nonneg (good a x)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun x _ => pointwise x)
  simpa only [uniformMass, adviceMass, ← Finset.mul_expect] using h

theorem adviceMass_ge_union_div_card
    {A X : Type*} [Fintype A] [Nonempty A] [Fintype X]
    (good : A → X → Prop) :
    uniformMass (goodUnion good) / (Fintype.card A : ℝ) ≤ adviceMass good := by
  have hcard : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  simpa [mul_comm] using union_mass_le_card_mul_adviceMass good

theorem adviceMass_ge_of_union_mass
    {A X : Type*} [Fintype A] [Nonempty A] [Fintype X]
    (good : A → X → Prop) (η : ℝ) (hη : η ≤ uniformMass (goodUnion good)) :
    η / (Fintype.card A : ℝ) ≤ adviceMass good := by
  exact (div_le_div_of_nonneg_right hη (Nat.cast_nonneg _)).trans
    (adviceMass_ge_union_div_card good)

end
end UniqueGamesTheorem.Inverse.RowErasure

end

section

/-!
The row-erasure union bound is eventually strictly below one. The number of
descriptions grows exponentially in `m`, while the tail exponent grows as
`2 ^ ((ell-r)*(m-r))`. The only asymptotic input is the standard proved limit
that a fixed polynomial divided by `2^n` tends to zero.
-/

namespace UniqueGamesTheorem.Inverse.RowErasure

open Filter
open scoped Topology

/-- Logarithm of the finite union-bound estimate, for every sufficiently large
column dimension. Neither the threshold nor the proof depends on a parity
condition on the column dimension. -/
theorem eventually_log_unionBound_neg (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∀ᶠ m : ℕ in atTop,
      (((2 * r + 1) * (ell + m) : ℕ) : ℝ) * Real.log 2 -
        α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32 < 0 := by
  let C : ℝ := (2 * r + 1 : ℕ)
  let D : ℝ := (ell + r : ℕ)
  have hzero : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_zero] using
      (tendsto_pow_const_div_const_pow_of_one_lt 0 (show (1 : ℝ) < 2 by norm_num))
  have hone : Tendsto (fun n : ℕ => (n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [pow_one] using
      (tendsto_pow_const_div_const_pow_of_one_lt 1 (show (1 : ℝ) < 2 by norm_num))
  have hlim' : Tendsto
      (fun n : ℕ => (C * Real.log 2) * (D * (1 / (2 : ℝ) ^ n) +
        (n : ℝ) / (2 : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((hzero.const_mul D).add hone).const_mul (C * Real.log 2)
  have hlim : Tendsto
      (fun n : ℕ => C * (D + (n : ℝ)) * Real.log 2 / (2 : ℝ) ^ n)
      atTop (𝓝 0) := by
    convert hlim' using 1
    ext n
    ring
  have hpos : 0 < α ^ 2 / 32 := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop,
      C * (D + (n : ℝ)) * Real.log 2 / (2 : ℝ) ^ n < α ^ 2 / 32 :=
    hlim.eventually (gt_mem_nhds hpos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  apply eventually_atTop.2
  refine ⟨N + r, ?_⟩
  intro m hm
  have hrm : r ≤ m := by omega
  have hn : N ≤ m - r := by omega
  have hmcast : (m : ℝ) = (r : ℝ) + ((m - r : ℕ) : ℝ) := by
    exact_mod_cast (show m = r + (m - r) by omega)
  have hcast : (((2 * r + 1) * (ell + m) : ℕ) : ℝ) =
      C * (D + ((m - r : ℕ) : ℝ)) := by
    dsimp [C, D]
    push_cast
    rw [hmcast]
    ring
  have hlinear := (div_lt_iff₀ (show (0 : ℝ) < 2 ^ (m - r) by positivity)).1
    (hN (m - r) hn)
  have hexponent : m - r ≤ (ell - r) * (m - r) := by
    have h := Nat.mul_le_mul_right (m - r) (show 1 ≤ ell - r by omega)
    simpa only [one_mul] using h
  have hpower : (2 : ℝ) ^ (m - r) ≤ 2 ^ ((ell - r) * (m - r)) :=
    pow_le_pow_right₀ (by norm_num) hexponent
  have hproduct := mul_le_mul_of_nonneg_left hpower hpos.le
  rw [hcast]
  nlinarith

/-- The exact description-count times tail estimate needed for simultaneous
row erasure is strictly below one in all sufficiently large dimensions. -/
theorem eventually_unionBound_lt_one (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∀ᶠ m : ℕ in atTop,
      (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) < 1 := by
  filter_upwards [eventually_log_unionBound_neg α hα ell r hr] with m hm
  have hpositive : (0 : ℝ) < 2 ^ ((2 * r + 1) * (ell + m)) := by positivity
  calc
    (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) =
        Real.exp ((((2 * r + 1) * (ell + m) : ℕ) : ℝ) * Real.log 2 -
          α ^ 2 * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) := by
      rw [← Real.exp_log hpositive, ← Real.exp_add, Real.log_pow]
      congr 1
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr hm

/-- A threshold usable by dimension-selection arguments, with enough columns
to accommodate all `r` prescribed column constraints. -/
theorem exists_unionBound_threshold (α : ℝ) (hα : 0 < α)
    (ell r : ℕ) (hr : r < ell) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → r ≤ m ∧
      (2 : ℝ) ^ ((2 * r + 1) * (ell + m)) *
        Real.exp (-(α ^ 2) * (2 : ℝ) ^ ((ell - r) * (m - r)) / 32) < 1 := by
  exact eventually_atTop.1 ((eventually_ge_atTop r).and
    (eventually_unionBound_lt_one α hα ell r hr))

end UniqueGamesTheorem.Inverse.RowErasure

end

section

/-!
Every nonempty affine row/column slice is an affine copy of the full space of
linear maps from the column quotient into the row kernel. This gives exact
uniform-law transport and preserves the affine evaluation offset.
-/

namespace UniqueGamesTheorem.Inverse.RowErasureSliceQuotient

noncomputable section

variable {R E K L : Type*} [Field R]
  [AddCommGroup E] [AddCommGroup K] [AddCommGroup L]
  [Module R E] [Module R K] [Module R L]

/-- The linear part of the affine parametrization. -/
def direction (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) : E →ₗ[R] K :=
  A.ker.subtype.comp (N.comp Q.mkQ)

@[simp] theorem direction_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (N : (E ⧸ Q) →ₗ[R] A.ker) (x : E) :
    direction A Q N x = (N (Q.mkQ x) : K) := rfl

/-- Quotient descent of a linear map which vanishes on the column span and
takes values in the common row kernel. -/
theorem exists_direction_of_row_and_column (A : K →ₗ[R] L)
    (Q : Submodule R E) (B : E →ₗ[R] K)
    (hQ : Q ≤ B.ker) (hA : LinearMap.range B ≤ A.ker) :
    ∃ N : (E ⧸ Q) →ₗ[R] A.ker, direction A Q N = B := by
  let B' : E →ₗ[R] A.ker := B.codRestrict A.ker
    (fun x => hA ⟨x, rfl⟩)
  have hQ' : Q ≤ B'.ker := by
    intro q hq
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change B q = 0
    exact hQ hq
  refine ⟨Q.liftQ B' hQ', ?_⟩
  ext x
  rfl

theorem direction_injective (A : K →ₗ[R] L) (Q : Submodule R E) :
    Function.Injective (direction A Q) := by
  intro N P h
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := Q.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : E →ₗ[R] K => f v) h

/-- The concrete affine slice around any one point satisfying its equations. -/
def AffineSlice (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K) :=
  {M : E →ₗ[R] K // A.comp M = A.comp M₀ ∧ ∀ q ∈ Q, M q = M₀ q}

def ofQuotient (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K)
    (N : (E ⧸ Q) →ₗ[R] A.ker) : AffineSlice A Q M₀ := by
  refine ⟨M₀ + direction A Q N, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change A (M₀ x + (N (Q.mkQ x) : K)) = A (M₀ x)
    rw [map_add, show A (N (Q.mkQ x) : K) = 0 from (N (Q.mkQ x)).property,
      add_zero]
  · intro q hq
    have hz : Q.mkQ q = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hq
    simp [direction, hz]

@[simp] theorem ofQuotient_val (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) :
    (ofQuotient A Q M₀ N).val = M₀ + direction A Q N := rfl

theorem ofQuotient_bijective (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) : Function.Bijective (ofQuotient A Q M₀) := by
  constructor
  · intro N P h
    apply direction_injective A Q
    exact add_left_cancel (congrArg Subtype.val h)
  · intro M
    have hQ : Q ≤ (M.val - M₀).ker := by
      intro q hq
      change M.val q - M₀ q = 0
      exact sub_eq_zero.mpr (M.property.2 q hq)
    have hA : LinearMap.range (M.val - M₀) ≤ A.ker := by
      rintro y ⟨x, rfl⟩
      change A (M.val x - M₀ x) = 0
      rw [map_sub]
      apply sub_eq_zero.mpr
      exact congrArg (fun f : E →ₗ[R] L => f x) M.property.1
    obtain ⟨N, hN⟩ := exists_direction_of_row_and_column A Q (M.val - M₀) hQ hA
    refine ⟨N, ?_⟩
    apply Subtype.ext
    rw [ofQuotient_val, hN]
    simpa only [← add_sub_assoc] using add_sub_cancel_left M₀ M.val

/-- Uniform free quotient maps parametrize exactly the original affine slice. -/
def equiv (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K) :
    ((E ⧸ Q) →ₗ[R] A.ker) ≃ AffineSlice A Q M₀ :=
  Equiv.ofBijective (ofQuotient A Q M₀) (ofQuotient_bijective A Q M₀)

@[simp] theorem equiv_apply (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) :
    equiv A Q M₀ N = ofQuotient A Q M₀ N := rfl

/-- The base point contributes an affine offset; it is not discarded. -/
theorem equiv_affine_target (A : K →ₗ[R] L) (Q : Submodule R E)
    (M₀ : E →ₗ[R] K) (N : (E ⧸ Q) →ₗ[R] A.ker) (z : E) (u : K) :
    (equiv A Q M₀ N).val z + u =
      (N (Q.mkQ z) : K) + (M₀ z + u) := by
  change (M₀ z + (N (Q.mkQ z) : K)) + u = _
  ac_rfl

/-- Exact uniform-law transport through the affine parametrization. -/
theorem expect_equiv (A : K →ₗ[R] L) (Q : Submodule R E) (M₀ : E →ₗ[R] K)
    [Fintype ((E ⧸ Q) →ₗ[R] A.ker)] [Fintype (AffineSlice A Q M₀)]
    (f : AffineSlice A Q M₀ → ℝ) :
    Finset.univ.expect (fun N => f (equiv A Q M₀ N)) = Finset.univ.expect f := by
  exact Fintype.expect_equiv (equiv A Q M₀) _ _ (fun _ => rfl)

end
end UniqueGamesTheorem.Inverse.RowErasureSliceQuotient

end

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators

noncomputable section

variable {X Y A S D : Type*}

/-- Each description includes its row map, row value, column equations and
affine target. `points_row` is the necessary relationship to actual row advice. -/
structure SliceFamily (X Y A S D : Type*) where
  advice : A → X → S
  rowMap : D → A
  rowValue : D → S
  points : D → Finset X
  target : D → X → Y
  points_row : ∀ d x, x ∈ points d → advice (rowMap d) x = rowValue d

def SliceFamily.agreement (F : SliceFamily X Y A S D) (f : X → Y) (d : D) : ℝ :=
  (F.points d).expect fun x => indicator (f x = F.target d x)

def SliceFamily.GoodAdvice (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (s : S) : Prop :=
  ∃ d, F.rowMap d = a ∧ F.rowValue d = s ∧ (F.points d).Nonempty ∧
    α / 2 ≤ F.agreement f d

def SliceFamily.goodAt (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) (a : A) (x : X) : Prop :=
  F.GoodAdvice f α a (F.advice a x)

def SliceFamily.erasedUnion (F : SliceFamily X Y A S D)
    (f : X → Y) (α : ℝ) : X → Prop :=
  goodUnion (F.goodAt f α)

/-- Only randomized entries count; an unchanged entry contributes zero, even
when its old label already matches the target. -/
def SliceFamily.randomizedAgreement (F : SliceFamily X Y A S D)
    (B : X → Prop) (replacement : X → Y) (d : D) : ℝ :=
  (F.points d).expect fun x => indicator (B x ∧ replacement x = F.target d x)

theorem SliceFamily.mem_erasedUnion_of_good_row
    (F : SliceFamily X Y A S D) (f : X → Y) (α : ℝ) (d : D)
    (good : F.GoodAdvice f α (F.rowMap d) (F.rowValue d))
    {x : X} (hx : x ∈ F.points d) : F.erasedUnion f α x := by
  refine ⟨F.rowMap d, ?_⟩
  change F.GoodAdvice f α (F.rowMap d) (F.advice (F.rowMap d) x)
  rw [F.points_row d x hx]
  exact good

theorem SliceFamily.original_agreement_lt_of_not_good
    (F : SliceFamily X Y A S D) (f : X → Y) (α : ℝ) (d : D)
    (hne : (F.points d).Nonempty)
    (not_good : ¬ F.GoodAdvice f α (F.rowMap d) (F.rowValue d)) :
    F.agreement f d < α / 2 := by
  by_contra h
  exact not_good ⟨d, rfl, rfl, hne, le_of_not_gt h⟩

theorem SliceFamily.modified_agreement_le_original_add_randomized
    (F : SliceFamily X Y A S D) (B : X → Prop)
    (f replacement : X → Y) (d : D) :
    F.agreement (replaceOn B f replacement) d ≤
      F.agreement f d + F.randomizedAgreement B replacement d := by
  classical
  have h := Finset.expect_le_expect (s := F.points d)
    (f := fun x => indicator (replaceOn B f replacement x = F.target d x))
    (g := fun x => indicator (f x = F.target d x) +
      indicator (B x ∧ replacement x = F.target d x)) (by
      intro x _
      by_cases hx : B x
      · rw [replaceOn_of_mem B f replacement hx]
        simp only [indicator, hx, true_and]
        have hnonneg := indicator_nonneg (f x = F.target d x)
        unfold indicator at hnonneg
        linarith
      · rw [replaceOn_of_not_mem B f replacement hx]
        simp [indicator, hx])
  simpa only [Finset.expect_add_distrib, SliceFamily.agreement,
    SliceFamily.randomizedAgreement] using h

theorem SliceFamily.modified_agreement_eq_randomized_of_good
    (F : SliceFamily X Y A S D) (f replacement : X → Y)
    (α : ℝ) (d : D)
    (good : F.GoodAdvice f α (F.rowMap d) (F.rowValue d)) :
    F.agreement (replaceOn (F.erasedUnion f α) f replacement) d =
      F.randomizedAgreement (F.erasedUnion f α) replacement d := by
  classical
  apply Finset.expect_congr rfl
  intro x hx
  have hB := F.mem_erasedUnion_of_good_row f α d good hx
  rw [replaceOn_of_mem _ f replacement hB]
  simp [indicator, hB]

/-- If the random replacement bound holds, *every* permitted nonempty slice
has modified agreement strictly below α. The proof splits on goodness of the
whole row fiber, not on goodness of the individual column slice. -/
theorem SliceFamily.modified_agreement_lt
    (F : SliceFamily X Y A S D) (f replacement : X → Y)
    (α : ℝ) (hα : 0 < α)
    (randomized_small : ∀ d, (F.points d).Nonempty →
      F.randomizedAgreement (F.erasedUnion f α) replacement d < α / 4)
    (d : D) (hne : (F.points d).Nonempty) :
    F.agreement (replaceOn (F.erasedUnion f α) f replacement) d < α := by
  classical
  by_cases hg : F.GoodAdvice f α (F.rowMap d) (F.rowValue d)
  · rw [F.modified_agreement_eq_randomized_of_good f replacement α d hg]
    have h := randomized_small d hne
    linarith
  · have ho := F.original_agreement_lt_of_not_good f α d hne hg
    have hr := randomized_small d hne
    have hm := F.modified_agreement_le_original_add_randomized
      (F.erasedUnion f α) f replacement d
    linarith

/-- Conditional erasure contradiction. The two deep inputs remain explicit:
the inverse theorem for arbitrary (possibly unfolded) functions, and existence
of a replacement table uniformly small on every slice/target description. -/
theorem SliceFamily.union_mass_ge_of_inverse_and_erasure
    {E : Type*} [Fintype X] [Fintype E]
    (F : SliceFamily X Y A S D) (left right : E → X)
    (f : X → Y) (η α : ℝ) (hη : 0 < η) (hα : 0 < α)
    (acceptance_large : 4 * η ≤ equalityAcceptance left right f)
    (left_uniform : ∀ B : X → Prop,
      uniformMass (fun e => B (left e)) = uniformMass B)
    (right_uniform : ∀ B : X → Prop,
      uniformMass (fun e => B (right e)) = uniformMass B)
    (inverse : ∀ g : X → Y, η ≤ equalityAcceptance left right g →
      ∃ d, (F.points d).Nonempty ∧ α ≤ F.agreement g d)
    (erasure : ∃ replacement : X → Y, ∀ d, (F.points d).Nonempty →
      F.randomizedAgreement (F.erasedUnion f α) replacement d < α / 4) :
    η ≤ uniformMass (F.erasedUnion f α) := by
  by_contra h
  have hsmall : uniformMass (F.erasedUnion f α) < η := lt_of_not_ge h
  obtain ⟨replacement, hr⟩ := erasure
  have hmodified := acceptance_ge_original_sub_two_mass left right
    (F.erasedUnion f α) f replacement
    (left_uniform (F.erasedUnion f α)) (right_uniform (F.erasedUnion f α))
  have haccept : η ≤ equalityAcceptance left right
      (replaceOn (F.erasedUnion f α) f replacement) := by linarith
  obtain ⟨d, hne, hd⟩ := inverse _ haccept
  have hlt := F.modified_agreement_lt f replacement α hα hr d hne
  linarith

end
end UniqueGamesTheorem.Inverse.RowErasure

end

section

namespace UniqueGamesTheorem.Inverse.RowErasure

open scoped BigOperators Classical

noncomputable section

theorem uniformMass_exists_le_sum
    {R D : Type*} [Fintype R] [Fintype D] (bad : D → R → Prop) :
    uniformMass (fun r => ∃ d, bad d r) ≤ ∑ d, uniformMass (bad d) := by
  classical
  have hp : ∀ r, indicator (∃ d, bad d r) ≤ ∑ d, indicator (bad d r) := by
    intro r
    by_cases hr : ∃ d, bad d r
    · obtain ⟨d, hd⟩ := hr
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset D)) (f := fun d => indicator (bad d r))
        (fun d _ => indicator_nonneg (bad d r)) (Finset.mem_univ d)
      simpa [indicator, hd, show ∃ d, bad d r from ⟨d, hd⟩] using h
    · simp only [indicator, ite_eq_right hr]
      exact Finset.sum_nonneg fun d _ => indicator_nonneg (bad d r)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun r _ => hp r)
  simpa only [uniformMass, Finset.expect_sum_comm] using h

theorem exists_avoiding_of_sum_bad_lt_one
    {R D : Type*} [Fintype R] [Nonempty R] [Fintype D]
    (bad : D → R → Prop) (hsmall : (∑ d, uniformMass (bad d)) < 1) :
    ∃ r, ∀ d, ¬ bad d r := by
  classical
  by_contra h
  have hall : ∀ r, ∃ d, bad d r := by
    intro r
    by_contra hr
    exact h ⟨r, fun d hd => hr ⟨d, hd⟩⟩
  have hm : uniformMass (fun r => ∃ d, bad d r) = 1 := by
    simp [uniformMass, indicator, hall]
  have hb := uniformMass_exists_le_sum bad
  rw [hm] at hb
  linarith

theorem exists_avoiding_of_card_mul_bound_lt_one
    {R D : Type*} [Fintype R] [Nonempty R] [Fintype D]
    (bad : D → R → Prop) (ρ : ℝ)
    (hprob : ∀ d, uniformMass (bad d) ≤ ρ)
    (hsmall : (Fintype.card D : ℝ) * ρ < 1) :
    ∃ r, ∀ d, ¬ bad d r := by
  apply exists_avoiding_of_sum_bad_lt_one bad
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset D)) (fun d _ => hprob d)
  have hsum : (∑ d, uniformMass (bad d)) ≤ (Fintype.card D : ℝ) * ρ := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  exact hsum.trans_lt hsmall

/-- The union-bound step for actual replacement tables. Nonempty slice
descriptions with randomized agreement at least α/4 are the bad events. -/
theorem SliceFamily.exists_erasure_of_probability_bound
    {X Y A S D : Type*} [Fintype X] [Fintype Y] [Nonempty Y] [Fintype D]
    (F : SliceFamily X Y A S D) (B : X → Prop) (α ρ : ℝ)
    (hprob : ∀ d, uniformMass (fun replacement : X → Y =>
      (F.points d).Nonempty ∧ α / 4 ≤ F.randomizedAgreement B replacement d) ≤ ρ)
    (hsmall : (Fintype.card D : ℝ) * ρ < 1) :
    ∃ replacement : X → Y, ∀ d, (F.points d).Nonempty →
      F.randomizedAgreement B replacement d < α / 4 := by
  obtain ⟨replacement, hr⟩ := exists_avoiding_of_card_mul_bound_lt_one
    (fun d replacement =>
      (F.points d).Nonempty ∧ α / 4 ≤ F.randomizedAgreement B replacement d)
    ρ hprob hsmall
  refine ⟨replacement, fun d hd => ?_⟩
  exact lt_of_not_ge (fun h => hr d ⟨hd, h⟩)

/-- Average the fixed-context advice bound over the spectral good contexts.
Both samples remain explicit: the context, then the row map and matrix. -/
theorem advice_average_ge
    {Q A X : Type*} [Fintype Q] [Fintype A] [Nonempty A] [Fintype X]
    (goodContext : Q → Prop) (good : Q → A → X → Prop)
    (β η : ℝ) (hη : 0 ≤ η)
    (hcontext : β ≤ uniformMass goodContext)
    (hlocal : ∀ q, goodContext q → η ≤ uniformMass (goodUnion (good q))) :
    β * (η / (Fintype.card A : ℝ)) ≤
      Finset.univ.expect (fun q => adviceMass (good q)) := by
  classical
  have hc : 0 ≤ η / (Fintype.card A : ℝ) :=
    div_nonneg hη (Nat.cast_nonneg _)
  have hp : ∀ q,
      indicator (goodContext q) * (η / (Fintype.card A : ℝ)) ≤ adviceMass (good q) := by
    intro q
    by_cases hq : goodContext q
    · simpa [indicator, hq] using adviceMass_ge_of_union_mass (good q) η (hlocal q hq)
    · simpa [indicator, hq] using adviceMass_nonneg (good q)
  have he := Finset.expect_le_expect (s := Finset.univ) (fun q _ => hp q)
  rw [← Finset.expect_mul] at he
  exact (mul_le_mul_of_nonneg_right hcontext hc).trans he

theorem advice_average_ge_ten_eta_sq_div_card
    {Q A X : Type*} [Fintype Q] [Fintype A] [Nonempty A] [Fintype X]
    (goodContext : Q → Prop) (good : Q → A → X → Prop)
    (η : ℝ) (hη : 0 ≤ η)
    (hcontext : 10 * η ≤ uniformMass goodContext)
    (hlocal : ∀ q, goodContext q → η ≤ uniformMass (goodUnion (good q))) :
    10 * η ^ 2 / (Fintype.card A : ℝ) ≤
      Finset.univ.expect (fun q => adviceMass (good q)) := by
  have h := advice_average_ge goodContext good (10 * η) η hη hcontext hlocal
  convert h using 1
  ring

end
end UniqueGamesTheorem.Inverse.RowErasure

end

end OAI

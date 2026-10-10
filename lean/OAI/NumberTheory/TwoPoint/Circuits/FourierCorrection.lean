import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace OAI

/-!
# Correcting an almost independent Boolean density

This is the finite Fourier correction used in the proof of the manuscript's
finite-residue comparison (`q:finite-law`, `q:fourier-correction-tv`). The
construction removes the chosen nonconstant Walsh coefficients and adds the
constant `a` before normalization, retaining pointwise nonnegativity.
-/

namespace TwoPointCorrelations

open Finset

abbrev BooleanCube (n : ℕ) := Fin n → Bool

/-- Uniform average on the finite Boolean cube. -/
noncomputable def cubeAverage {n : ℕ} (f : BooleanCube n → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card (BooleanCube n)

lemma cubeAverage_add {n : ℕ} (f g : BooleanCube n → ℝ) :
    cubeAverage (fun x => f x + g x) = cubeAverage f + cubeAverage g := by
  simp [cubeAverage, Finset.sum_add_distrib, add_div]

lemma cubeAverage_sub {n : ℕ} (f g : BooleanCube n → ℝ) :
    cubeAverage (fun x => f x - g x) = cubeAverage f - cubeAverage g := by
  simp [cubeAverage, Finset.sum_sub_distrib, sub_div]

lemma cubeAverage_mul_const {n : ℕ} (f : BooleanCube n → ℝ) (c : ℝ) :
    cubeAverage (fun x => c * f x) = c * cubeAverage f := by
  simp only [cubeAverage, ← Finset.mul_sum, mul_div_assoc]

@[simp] lemma cubeAverage_const {n : ℕ} (c : ℝ) :
    cubeAverage (fun _ : BooleanCube n => c) = c := by
  simp [cubeAverage, Finset.sum_const]

lemma cubeAverage_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → BooleanCube n → ℝ) :
    cubeAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeAverage (f i) := by
  simp only [cubeAverage, Finset.sum_div]
  rw [Finset.sum_comm]

lemma cubeAverage_mono {n : ℕ} {f g : BooleanCube n → ℝ}
    (h : ∀ x, f x ≤ g x) : cubeAverage f ≤ cubeAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (by positivity)

/-- The sign representation of a Boolean coordinate. -/
def booleanSign (b : Bool) : ℝ := if b then -1 else 1

@[simp] lemma booleanSign_not (b : Bool) : booleanSign (!b) = -booleanSign b := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma booleanSign_sq (b : Bool) : booleanSign b * booleanSign b = 1 := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma abs_booleanSign (b : Bool) : |booleanSign b| = 1 := by
  cases b <;> norm_num [booleanSign]

/-- The Walsh character indexed by a coordinate set. -/
def walsh {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) : ℝ :=
  ∏ i ∈ S, booleanSign (x i)

@[simp] lemma walsh_empty {n : ℕ} (x : BooleanCube n) : walsh ∅ x = 1 := by
  simp [walsh]

@[simp] lemma abs_walsh {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    |walsh S x| = 1 := by
  simp [walsh, Finset.abs_prod]

@[simp] lemma walsh_mul_self {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    walsh S x * walsh S x = 1 := by
  unfold walsh
  rw [← Finset.prod_mul_distrib]
  simp

/-- The measure-preserving involution that reverses one coordinate. -/
def flipBit {n : ℕ} (i : Fin n) : BooleanCube n ≃ BooleanCube n where
  toFun x := Function.update x i (!x i)
  invFun x := Function.update x i (!x i)
  left_inv x := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  right_inv x := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]

lemma walsh_flipBit {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (x : BooleanCube n) :
    walsh S (flipBit i x) = if i ∈ S then -walsh S x else walsh S x := by
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    have hrest : (∏ j ∈ S.erase i, booleanSign ((flipBit i x) j)) =
        ∏ j ∈ S.erase i, booleanSign (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [flipBit, Function.update_of_ne (mem_erase.mp hj).1]
    unfold walsh
    rw [← Finset.prod_erase_mul _ _ hi, hrest,
      ← Finset.prod_erase_mul _ (fun j => booleanSign (x j)) hi]
    simp [flipBit]
  · rw [ite_eq_right hi]
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    simp [flipBit, Function.update_of_ne hji]

lemma cubeAverage_eq_zero_of_flip {n : ℕ} (f : BooleanCube n → ℝ) (i : Fin n)
    (hf : ∀ x, f (flipBit i x) = -f x) : cubeAverage f = 0 := by
  have hsum : (∑ x, f (flipBit i x)) = ∑ x, f x :=
    (flipBit i).sum_comp f
  simp_rw [hf] at hsum
  rw [Finset.sum_neg_distrib] at hsum
  have hz : (∑ x, f x) = 0 := by linarith
  simp [cubeAverage, hz]

lemma cubeAverage_walsh {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty) :
    cubeAverage (walsh S) = 0 := by
  obtain ⟨i, hi⟩ := hS
  apply cubeAverage_eq_zero_of_flip _ i
  intro x
  simp [walsh_flipBit, hi]

lemma cubeAverage_walsh_mul {n : ℕ} (S T : Finset (Fin n)) :
    cubeAverage (fun x => walsh S x * walsh T x) = if S = T then 1 else 0 := by
  classical
  by_cases hST : S = T
  · subst T; simp
  · rw [ite_eq_right hST]
    have hex : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      simpa only [Finset.ext_iff, not_forall] using hST
    obtain ⟨i, hi⟩ := hex
    apply cubeAverage_eq_zero_of_flip _ i
    intro x
    by_cases hSi : i ∈ S
    · have hTi : i ∉ T := fun h => hi ⟨fun _ => h, fun _ => hSi⟩
      simp [walsh_flipBit, hSi, hTi]
    · have hTi : i ∈ T := by
        by_contra hnot
        apply hi
        simp [hSi, hnot]
      simp [walsh_flipBit, hSi, hTi]

/-- Nonempty coordinate sets through order `t`. -/
def lowWalshSets (n t : ℕ) : Finset (Finset (Fin n)) :=
  univ.filter (fun S => S.Nonempty ∧ S.card ≤ t)

noncomputable def walshCoefficient {n : ℕ} (f : BooleanCube n → ℝ)
    (S : Finset (Fin n)) : ℝ := cubeAverage (fun x => f x * walsh S x)

noncomputable def lowWalshCorrection {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (x : BooleanCube n) : ℝ :=
  ∑ S ∈ lowWalshSets n t, walshCoefficient f S * walsh S x

noncomputable def lowWalshMass {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) : ℝ :=
  ∑ S ∈ lowWalshSets n t, |walshCoefficient f S|

lemma cubeAverage_lowWalshCorrection {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) :
    cubeAverage (lowWalshCorrection f t) = 0 := by
  change cubeAverage (fun x => ∑ S ∈ lowWalshSets n t, walshCoefficient f S * walsh S x) = 0
  rw [cubeAverage_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [cubeAverage_mul_const, cubeAverage_walsh (mem_filter.mp hS).2.1, mul_zero]

lemma lowWalshCorrection_abs_le {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (x : BooleanCube n) : |lowWalshCorrection f t x| ≤ lowWalshMass f t := by
  unfold lowWalshCorrection lowWalshMass
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  simp

lemma lowWalshCorrection_coefficient {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (S : Finset (Fin n)) (hS : S ∈ lowWalshSets n t) :
    cubeAverage (fun x => lowWalshCorrection f t x * walsh S x) = walshCoefficient f S := by
  simp only [lowWalshCorrection, Finset.sum_mul]
  rw [cubeAverage_sum]
  simp_rw [mul_assoc, cubeAverage_mul_const, cubeAverage_walsh_mul]
  simp [hS]

/-- Add a constant after removing low Walsh modes, then renormalize. -/
noncomputable def correctedCubeDensity {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (a : ℝ) (x : BooleanCube n) : ℝ :=
  (f x - lowWalshCorrection f t x + a) / (1 + a)

lemma correctedCubeDensity_nonneg {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) (a : ℝ)
    (hf : ∀ x, 0 ≤ f x) (ha : 0 ≤ a) (hmass : lowWalshMass f t ≤ a) :
    ∀ x, 0 ≤ correctedCubeDensity f t a x := by
  intro x
  apply div_nonneg _ (by linarith)
  have hH := (le_abs_self (lowWalshCorrection f t x)).trans
    ((lowWalshCorrection_abs_le f t x).trans hmass)
  linarith [hf x]

lemma cubeAverage_correctedCubeDensity {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (a : ℝ) (hf : cubeAverage f = 1) (ha : 0 ≤ a) :
    cubeAverage (correctedCubeDensity f t a) = 1 := by
  have hden : 1 + a ≠ 0 := by linarith
  unfold correctedCubeDensity
  simp only [div_eq_mul_inv]
  simp_rw [mul_comm _ (1 + a)⁻¹]
  rw [cubeAverage_mul_const, cubeAverage_add, cubeAverage_sub,
    hf, cubeAverage_lowWalshCorrection, cubeAverage_const]
  field_simp
  ring

lemma correctedCubeDensity_coefficient {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (a : ℝ) (S : Finset (Fin n)) (hS : S ∈ lowWalshSets n t) :
    walshCoefficient (correctedCubeDensity f t a) S = 0 := by
  unfold walshCoefficient correctedCubeDensity
  have heq : (fun x => (f x - lowWalshCorrection f t x + a) / (1 + a) * walsh S x) =
      fun x => (1 + a)⁻¹ *
        ((f x * walsh S x - lowWalshCorrection f t x * walsh S x) + a * walsh S x) := by
    funext x
    ring
  rw [heq, cubeAverage_mul_const, cubeAverage_add, cubeAverage_sub,
    lowWalshCorrection_coefficient f t S hS, cubeAverage_mul_const,
    cubeAverage_walsh (mem_filter.mp hS).2.1]
  change (1 + a)⁻¹ * (walshCoefficient f S - walshCoefficient f S + a * 0) = 0
  ring

/-- Total variation from the initial density is at most `3a/2`. -/
theorem correctedCubeDensity_totalVariation_le {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (a : ℝ) (hf : ∀ x, 0 ≤ f x) (hmean : cubeAverage f = 1)
    (ha : 0 ≤ a) (hmass : lowWalshMass f t ≤ a) :
    cubeAverage (fun x => |correctedCubeDensity f t a x - f x|) / 2 ≤ 3 * a / 2 := by
  have hden : 0 < 1 + a := by linarith
  have hpoint (x : BooleanCube n) :
      |correctedCubeDensity f t a x - f x| ≤ a * (2 + f x) := by
    have hdiff : correctedCubeDensity f t a x - f x =
        (-lowWalshCorrection f t x + a * (1 - f x)) / (1 + a) := by
      unfold correctedCubeDensity
      field_simp
      ring
    rw [hdiff, abs_div, abs_of_pos hden]
    apply (div_le_self (abs_nonneg _) (by linarith : 1 ≤ 1 + a)).trans
    have hH := (lowWalshCorrection_abs_le f t x).trans hmass
    have hF : |1 - f x| ≤ 1 + f x := by
      rw [abs_le]
      constructor <;> linarith [hf x]
    calc
      |-lowWalshCorrection f t x + a * (1 - f x)| ≤
          |lowWalshCorrection f t x| + a * |1 - f x| := by
        simpa [abs_mul, abs_of_nonneg ha] using
          abs_add_le (-lowWalshCorrection f t x) (a * (1 - f x))
      _ ≤ a + a * (1 + f x) := add_le_add hH (mul_le_mul_of_nonneg_left hF ha)
      _ = a * (2 + f x) := by ring
  have hav := cubeAverage_mono hpoint
  rw [cubeAverage_mul_const, cubeAverage_add, cubeAverage_const, hmean] at hav
  linarith

/-- Indicator of a prescribed pattern on a set of coordinates. -/
noncomputable def cubePattern {n : ℕ} (S : Finset (Fin n))
    (z x : BooleanCube n) : ℝ := if ∀ i ∈ S, x i = z i then 1 else 0

/-- Finite Walsh inversion of a cylinder indicator. -/
lemma cubePattern_walsh_expansion {n : ℕ} (S : Finset (Fin n))
    (z x : BooleanCube n) :
    (2 : ℝ) ^ S.card * cubePattern S z x =
      ∑ T ∈ S.powerset, walsh T z * walsh T x := by
  have hcoord (i : Fin n) : 1 + booleanSign (z i) * booleanSign (x i) =
      if x i = z i then (2 : ℝ) else 0 := by
    cases hx : x i <;> cases hz : z i <;> norm_num [booleanSign, hx, hz]
  have hprod : (∏ i ∈ S, (1 + booleanSign (z i) * booleanSign (x i))) =
      (2 : ℝ) ^ S.card * cubePattern S z x := by
    by_cases h : ∀ i ∈ S, x i = z i
    · calc
        (∏ i ∈ S, (1 + booleanSign (z i) * booleanSign (x i))) =
            ∏ _i ∈ S, (2 : ℝ) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [hcoord, ite_eq_left (h i hi)]
        _ = (2 : ℝ) ^ S.card * cubePattern S z x := by
          rw [cubePattern, ite_eq_left h]
          simp
    · have hex : ∃ i ∈ S, x i ≠ z i := by
        push Not at h
        exact h
      obtain ⟨i, hi, hneq⟩ := hex
      have hz : (∏ i ∈ S, (1 + booleanSign (z i) * booleanSign (x i))) = 0 := by
        apply Finset.prod_eq_zero hi
        rw [hcoord, ite_eq_right hneq]
      simp [hz, cubePattern, h]
  rw [← hprod, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.prod_mul_distrib]
  rfl

/-- Vanishing of all nonconstant Walsh coefficients on a coordinate set makes
that marginal exactly uniform. -/
lemma cubeAverage_pattern_of_walsh {n : ℕ} (g : BooleanCube n → ℝ)
    (S : Finset (Fin n)) (z : BooleanCube n) (hmean : cubeAverage g = 1)
    (hcoeff : ∀ T ⊆ S, T.Nonempty → walshCoefficient g T = 0) :
    cubeAverage (fun x => g x * cubePattern S z x) = 1 / (2 : ℝ) ^ S.card := by
  have hsum : (∑ T ∈ S.powerset, walsh T z * walshCoefficient g T) = 1 := by
    rw [Finset.sum_eq_single ∅]
    · simpa [walshCoefficient] using hmean
    · intro T hT hne
      rw [hcoeff T (mem_powerset.mp hT) (Finset.nonempty_iff_ne_empty.mpr hne), mul_zero]
    · simp
  have hscale : (2 : ℝ) ^ S.card * cubeAverage (fun x => g x * cubePattern S z x) = 1 := by
    calc
      (2 : ℝ) ^ S.card * cubeAverage (fun x => g x * cubePattern S z x) =
          cubeAverage (fun x => (2 : ℝ) ^ S.card * (g x * cubePattern S z x)) :=
        (cubeAverage_mul_const _ _).symm
      _ = cubeAverage (fun x => ∑ T ∈ S.powerset,
          walsh T z * (g x * walsh T x)) := by
        congr 1
        funext x
        rw [mul_left_comm, cubePattern_walsh_expansion, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        ring
      _ = ∑ T ∈ S.powerset, walsh T z * walshCoefficient g T := by
        rw [cubeAverage_sum]
        apply Finset.sum_congr rfl
        intro T hT
        exact cubeAverage_mul_const _ _
      _ = 1 := hsum
  apply (eq_div_iff (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))).mpr
  nlinarith only [hscale]

/-- Every assignment to at most `t` selected coordinates has its uniform mass. -/
def TWiseUniformDensity {n : ℕ} (g : BooleanCube n → ℝ) (t : ℕ) : Prop :=
  ∀ (S : Finset (Fin n)), S.card ≤ t → ∀ z : BooleanCube n,
    cubeAverage (fun x => g x * cubePattern S z x) = 1 / (2 : ℝ) ^ S.card

lemma correctedCubeDensity_tWiseUniform {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (a : ℝ) (hmean : cubeAverage f = 1) (ha : 0 ≤ a) :
    TWiseUniformDensity (correctedCubeDensity f t a) t := by
  intro S hS z
  apply cubeAverage_pattern_of_walsh _ S z (cubeAverage_correctedCubeDensity f t a hmean ha)
  intro T hTS hT
  apply correctedCubeDensity_coefficient
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ T,
    hT, (Finset.card_le_card hTS).trans hS⟩

/-- The complete finite correction used before applying Braverman's theorem. -/
theorem fourierCorrection {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) (a : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hmean : cubeAverage f = 1)
    (ha : 0 ≤ a) (hmass : lowWalshMass f t ≤ a) :
    (∀ x, 0 ≤ correctedCubeDensity f t a x) ∧
      cubeAverage (correctedCubeDensity f t a) = 1 ∧
      TWiseUniformDensity (correctedCubeDensity f t a) t ∧
      cubeAverage (fun x => |correctedCubeDensity f t a x - f x|) / 2 ≤ 3 * a / 2 :=
  ⟨correctedCubeDensity_nonneg f t a hf ha hmass,
    cubeAverage_correctedCubeDensity f t a hmean ha,
    correctedCubeDensity_tWiseUniform f t a hmean ha,
    correctedCubeDensity_totalVariation_le f t a hf hmean ha hmass⟩

end TwoPointCorrelations

end OAI

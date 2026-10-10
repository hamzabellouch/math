import OAI.Combinatorics.ProgressionColoring.TernarySign
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

universe uIndex

namespace QuantitativeVanDerWaerden

open scoped BigOperators

/-- A real affine form in `e` parameters. -/
structure AffineForm (e : ℕ) where
  linear : Fin e → ℝ
  constant : ℝ

def AffineForm.eval {e : ℕ} (f : AffineForm e) (x : Fin e → ℝ) : ℝ :=
  (∑ j, f.linear j * x j) + f.constant

def signVector {e s : ℕ} (forms : Fin s → AffineForm e) (x : Fin e → ℝ) :
    Fin s → Fin 3 := fun i => ternarySign ((forms i).eval x)

/-- Realized patterns on any specified parameter subset. -/
def realizedSigns {e s : ℕ} (forms : Fin s → AffineForm e)
    (D : Set (Fin e → ℝ)) : Finset (Fin s → Fin 3) := by
  classical
  exact Finset.univ.filter (fun p => ∃ x ∈ D, signVector forms x = p)

@[simp] theorem mem_realizedSigns {e s : ℕ} (forms : Fin s → AffineForm e)
    (D : Set (Fin e → ℝ)) (p : Fin s → Fin 3) :
    p ∈ realizedSigns forms D ↔ ∃ x ∈ D, signVector forms x = p := by
  classical
  simp [realizedSigns]

namespace Arrangement

def linearValue {d : ℕ} (v x : Fin d → ℝ) : ℝ := ∑ j, v j * x j

private theorem linearValue_smul {d : ℕ} (c : ℝ) (v x : Fin d → ℝ) :
    linearValue (c • v) x = c * linearValue v x := by
  simp [linearValue, Finset.mul_sum, mul_assoc]

private theorem linearValue_sum {ι : Type uIndex} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (x : Fin d → ℝ) :
    linearValue (∑ i, v i) x = ∑ i, linearValue (v i) x := by
  simp only [linearValue, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

private theorem linearValue_neg {d : ℕ} (v x : Fin d → ℝ) :
    linearValue v (-x) = -linearValue v x := by
  simp [linearValue, Finset.sum_neg_distrib]

section StrictSupports

variable {ι : Type uIndex} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- All strict homogeneous threshold supports of the fixed coefficient vectors. -/
def thresholdFamily (v : ι → Fin d → ℝ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (fun t => ∃ x, ∀ i, i ∈ t ↔ 0 < linearValue (v i) x)

@[simp] theorem mem_thresholdFamily {ι : Type uIndex} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (v : ι → Fin d → ℝ) (t : Finset ι) :
    t ∈ thresholdFamily v ↔ ∃ x, ∀ i, i ∈ t ↔ 0 < linearValue (v i) x := by
  classical
  simp [thresholdFamily]

/-- Shattering realizes the positive support of any coefficients on the set. -/
private theorem separates_coefficients (v : ι → Fin d → ℝ) (s : Finset ι)
    (hs : (thresholdFamily v).Shatters s) (c : s → ℝ) :
    ∃ x : Fin d → ℝ, ∀ i : s, 0 < linearValue (v i) x ↔ 0 < c i := by
  classical
  let t := s.filter (fun i => ∃ hi : i ∈ s, 0 < c ⟨i, hi⟩)
  have hts : t ⊆ s := Finset.filter_subset _ _
  obtain ⟨u, hu, hsu⟩ := hs hts
  obtain ⟨x, hx⟩ := (mem_thresholdFamily v u).mp hu
  refine ⟨x, fun i => ?_⟩
  have hi : (i : ι) ∈ u ↔ (i : ι) ∈ t := by
    have h := congrArg (fun a : Finset ι => (i : ι) ∈ a) hsu
    simpa only [Finset.mem_inter, i.property, true_and] using (Iff.of_eq h)
  rw [← hx (i : ι), hi]
  simp [t]

/-- A vanishing linear combination has no positive coefficient: choose
its own positive support, making every scalar product nonnegative. -/
private theorem coefficients_nonpos (v : ι → Fin d → ℝ) (s : Finset ι)
    (hs : (thresholdFamily v).Shatters s) (c : s → ℝ)
    (hc : ∑ i : s, c i • v i = 0) : ∀ i, c i ≤ 0 := by
  classical
  obtain ⟨x, hx⟩ := separates_coefficients v s hs c
  have hsum : (∑ i : s, c i * linearValue (v i) x) = 0 := by
    calc
      _ = linearValue (∑ i : s, c i • v i) x := by
        rw [linearValue_sum]
        exact Finset.sum_congr rfl (fun i _ => (linearValue_smul (c i) (v i) x).symm)
      _ = 0 := by rw [hc]; simp [linearValue]
  have hnonneg (i : s) : 0 ≤ c i * linearValue (v i) x := by
    by_cases hi : 0 < c i
    · exact mul_nonneg hi.le ((hx i).mpr hi).le
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hi)
        (le_of_not_gt (fun h => hi ((hx i).mp h)))
  intro i
  by_contra hi
  have hcpos : 0 < c i := lt_of_not_ge hi
  have hterm : c i * linearValue (v i) x ≤ 0 := by
    calc
      _ ≤ ∑ j : s, c j * linearValue (v j) x :=
        Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      _ = 0 := hsum
  exact (not_lt_of_ge hterm) (mul_pos hcpos ((hx i).mpr hcpos))

/-- Every shattered coefficient subfamily is genuinely linearly independent. -/
theorem shatters_linearIndependent (v : ι → Fin d → ℝ) (s : Finset ι)
    (hs : (thresholdFamily v).Shatters s) :
    LinearIndependent ℝ (fun i : s => v i) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hnonpos := coefficients_nonpos v s hs c hc i
  have hneg : (∑ j : s, (-c j) • v j) = 0 := by
    simp only [neg_smul, Finset.sum_neg_distrib, hc, neg_zero]
  have hnonneg := coefficients_nonpos v s hs (fun j => -c j) hneg i
  linarith

theorem shatters_card_le (v : ι → Fin d → ℝ) (s : Finset ι)
    (hs : (thresholdFamily v).Shatters s) : s.card ≤ d := by
  simpa only [Fintype.card_coe, Module.finrank_fin_fun] using
    (shatters_linearIndependent v s hs).fintype_card_le_finrank

theorem thresholdFamily_vcDim_le (v : ι → Fin d → ℝ) :
    (thresholdFamily v).vcDim ≤ d := by
  classical
  apply Finset.sup_le
  intro s hs
  exact shatters_card_le v s (Finset.mem_shatterer.mp hs)

/-- Sauer--Shelah, with the dimension premise proved above, gives a
uniform polynomial bound for all strict homogeneous supports. -/
theorem card_thresholdFamily_le (v : ι → Fin d → ℝ) :
    (thresholdFamily v).card ≤ (d + 1) * (Fintype.card ι + 1) ^ d := by
  classical
  calc
    (thresholdFamily v).card ≤ (thresholdFamily v).shatterer.card :=
      Finset.card_le_card_shatterer _
    _ ≤ ∑ k ∈ Finset.Iic (thresholdFamily v).vcDim, (Fintype.card ι).choose k :=
      Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card ι).choose k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hk).trans (thresholdFamily_vcDim_le v))
      · intro k _ _
        exact Nat.zero_le _
    _ ≤ ∑ _k ∈ Finset.Iic d, (Fintype.card ι + 1) ^ d := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        (Fintype.card ι).choose k ≤ (Fintype.card ι) ^ k := Nat.choose_le_pow _ _
        _ ≤ (Fintype.card ι + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ _) _
        _ ≤ (Fintype.card ι + 1) ^ d :=
          Nat.pow_le_pow_right (Nat.succ_pos _) (Finset.mem_Iic.mp hk)
    _ = (d + 1) * (Fintype.card ι + 1) ^ d := by simp

end StrictSupports

/-- The constant coefficient is the first coordinate of the homogeneous lift. -/
def liftedCoefficients {e : ℕ} (f : AffineForm e) : Fin (e + 1) → ℝ :=
  Fin.cons f.constant f.linear

def liftedPoint {e : ℕ} (x : Fin e → ℝ) : Fin (e + 1) → ℝ := Fin.cons 1 x

theorem linearValue_lift {e : ℕ} (f : AffineForm e) (x : Fin e → ℝ) :
    linearValue (liftedCoefficients f) (liftedPoint x) = f.eval x := by
  simp [linearValue, liftedCoefficients, liftedPoint, AffineForm.eval,
    Fin.sum_univ_succ, add_comm]

def signEncoding {s : ℕ} (p : Fin s → Fin 3) : Finset (Fin s) × Finset (Fin s) :=
  (Finset.univ.filter (fun i => p i = 2), Finset.univ.filter (fun i => p i = 0))

private theorem fin_three_ext {a b : Fin 3}
    (hzero : a = 0 ↔ b = 0) (htwo : a = 2 ↔ b = 2) : a = b := by
  fin_cases a <;> fin_cases b <;> simp_all

theorem signEncoding_injective {s : ℕ} : Function.Injective (@signEncoding s) := by
  intro p q hpq
  funext i
  apply fin_three_ext
  · have h := congrArg (fun a : Finset (Fin s) × Finset (Fin s) => i ∈ a.2) hpq
    simpa [signEncoding] using (Iff.of_eq h)
  · have h := congrArg (fun a : Finset (Fin s) × Finset (Fin s) => i ∈ a.1) hpq
    simpa [signEncoding] using (Iff.of_eq h)

theorem signVector_encoding_mem {e s : ℕ} (forms : Fin s → AffineForm e)
    (x : Fin e → ℝ) :
    signEncoding (signVector forms x) ∈
      (thresholdFamily (fun i => liftedCoefficients (forms i))).product
        (thresholdFamily (fun i => liftedCoefficients (forms i))) := by
  classical
  apply Finset.mem_product.mpr
  constructor
  · apply (mem_thresholdFamily _ _).mpr
    refine ⟨liftedPoint x, fun i => ?_⟩
    simp [signEncoding, signVector, linearValue_lift]
  · apply (mem_thresholdFamily _ _).mpr
    refine ⟨-liftedPoint x, fun i => ?_⟩
    simp [signEncoding, signVector, linearValue_neg, linearValue_lift]

end Arrangement

/-- Polynomial arrangement bound, including zero signs and arbitrary
restrictions of the parameter domain. Its degree is independent of `s`. -/
theorem card_realizedSigns_le {e s : ℕ} (forms : Fin s → AffineForm e)
    (D : Set (Fin e → ℝ)) :
    (realizedSigns forms D).card ≤ (e + 2) ^ 2 * (s + 1) ^ (2 * (e + 1)) := by
  classical
  let v := fun i => Arrangement.liftedCoefficients (forms i)
  have hcard : (realizedSigns forms D).card ≤
      (Arrangement.thresholdFamily v).card * (Arrangement.thresholdFamily v).card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn Arrangement.signEncoding
    · intro p hp
      obtain ⟨x, _, rfl⟩ := (mem_realizedSigns forms D p).mp hp
      exact Arrangement.signVector_encoding_mem forms x
    · exact Arrangement.signEncoding_injective.injOn
  have hbound : (Arrangement.thresholdFamily v).card ≤ (e + 2) * (s + 1) ^ (e + 1) := by
    simpa only [Fintype.card_fin, Nat.add_assoc] using Arrangement.card_thresholdFamily_le v
  calc
    _ ≤ ((e + 2) * (s + 1) ^ (e + 1)) * ((e + 2) * (s + 1) ^ (e + 1)) :=
      hcard.trans (Nat.mul_le_mul hbound hbound)
    _ = (e + 2) ^ 2 * (s + 1) ^ (2 * (e + 1)) := by
      rw [two_mul, pow_add]
      ring

end QuantitativeVanDerWaerden

end

end OAI

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Finite bins for probability coefficients

An integer floor grid partitions the coefficient simplex into finitely many
parts of arbitrarily small l1 diameter. The proof uses only the Archimedean
property and finite sums, and also applies when the coefficient index is empty.
-/

open scoped BigOperators

namespace Tingley

/-- Nonnegative coefficients with total mass one. -/
def CoefficientSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

private theorem coefficient_le_one {n : ℕ} {w : Fin n → ℝ}
    (hw : w ∈ CoefficientSimplex n) (i : Fin n) : w i ≤ 1 := by
  calc
    w i ≤ ∑ j, w j :=
      Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
    _ = 1 := hw.2

private theorem abs_sub_lt_of_same_floor {K a b : ℝ} {q : ℕ}
    (hK : 0 < K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hqa : Nat.floor (K * a) = q) (hqb : Nat.floor (K * b) = q) :
    |a - b| < 1 / K := by
  have ha' := (Nat.floor_eq_iff (mul_nonneg hK.le ha)).mp hqa
  have hb' := (Nat.floor_eq_iff (mul_nonneg hK.le hb)).mp hqb
  have hab : a - b < 1 / K := by
    apply (lt_div_iff₀' hK).mpr
    nlinarith only [ha'.2, hb'.1]
  have hba : b - a < 1 / K := by
    apply (lt_div_iff₀' hK).mpr
    nlinarith only [hb'.2, ha'.1]
  exact abs_lt.mpr ⟨by linarith only [hba], hab⟩

/-- A finite family of coefficient bins with l1 diameter at most `η`.

The label type has `(K + 1)^n` elements. The last coordinate label retains
coefficients equal to one. For `n = 0`, the simplex and all bins are empty;
no nonemptiness hypothesis on the coefficient index is needed.
-/
theorem exists_coefficient_bins (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∃ bins : (Fin n → Fin (K + 1)) → Set (Fin n → ℝ),
      (∀ w ∈ CoefficientSimplex n, ∃ q, w ∈ bins q) ∧
      (∀ q, ∀ w ∈ bins q, ∀ v ∈ bins q, ∑ i, |w i - v i| ≤ η) := by
  obtain ⟨K, hgrid⟩ := exists_nat_gt ((n : ℝ) / η)
  have hK : (0 : ℝ) < K :=
    lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg n) hη.le) hgrid
  have hsmall : (n : ℝ) / K < η := by
    apply (div_lt_iff₀ hK).mpr
    simpa only [mul_comm] using (div_lt_iff₀ hη).mp hgrid
  let bins : (Fin n → Fin (K + 1)) → Set (Fin n → ℝ) := fun q =>
    {w | w ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * w i) = (q i).val}
  refine ⟨K, bins, ?_, ?_⟩
  · intro w hw
    have hcode (i : Fin n) : Nat.floor ((K : ℝ) * w i) < K + 1 := by
      apply Nat.lt_succ_of_le
      apply Nat.floor_le_of_le
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (coefficient_le_one hw i) hK.le
    let q : Fin n → Fin (K + 1) := fun i =>
      ⟨Nat.floor ((K : ℝ) * w i), hcode i⟩
    refine ⟨q, ?_⟩
    change w ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * w i) = (q i).val
    exact ⟨hw, fun _ => rfl⟩
  · intro q w hw v hv
    change (w ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * w i) = (q i).val) at hw
    change (v ∈ CoefficientSimplex n ∧
      ∀ i, Nat.floor ((K : ℝ) * v i) = (q i).val) at hv
    have hcoord (i : Fin n) : |w i - v i| < 1 / (K : ℝ) :=
      abs_sub_lt_of_same_floor hK (hw.1.1 i) (hv.1.1 i) (hw.2 i) (hv.2 i)
    calc
      ∑ i, |w i - v i| ≤ ∑ _i : Fin n, 1 / (K : ℝ) :=
        Finset.sum_le_sum (fun i _ => (hcoord i).le)
      _ = (n : ℝ) / K := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one_div]
      _ ≤ η := hsmall.le

end Tingley

end OAI

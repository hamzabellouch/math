import OAI.Combinatorics.ContingencyTables.Rooted.RootedCountingSchedule
import Mathlib.Data.Rat.Floor

namespace OAI

/-! # Executing the terminal coefficient without real logarithms

The source's ceiling of log₂(1/epsilon) is exactly the natural ceiling
logarithm of ceil(1/epsilon). All terminal metadata can therefore be
computed with natural and rational arithmetic.
-/

namespace ContingencyTables.CountingTerminalSchedule

open CompanionFactorialApplication CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

lemma natCeil_ratCast (q : ℚ) : ⌈(q:ℝ)⌉₊=⌈q⌉₊ := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    exact_mod_cast Nat.le_ceil q
  · apply Nat.ceil_le.mpr
    exact_mod_cast Nat.le_ceil (q:ℝ)

def precision (epsilon : ℚ) : ℕ := Nat.clog 2 ⌈1/epsilon⌉₊
def allowance (L d : ℕ) (epsilon : ℚ) : ℕ := 20*(L+d+precision epsilon+1)
def coefficient (L d : ℕ) (epsilon : ℚ) : ℕ :=
  ⌈(2048:ℚ)*d*(allowance L d epsilon)^2/epsilon⌉₊

lemma precision_eq (epsilon : ℚ) (he : 0 < epsilon) :
    precision epsilon=CompanionTerminalParameters.precision (epsilon:ℝ) := by
  have heR : (0:ℝ) < epsilon := by exact_mod_cast he
  have hequiv (n : ℕ) :
      CompanionTerminalParameters.precision (epsilon:ℝ) ≤ n ↔ precision epsilon ≤ n := by
    rw [CompanionTerminalParameters.precision,Nat.ceil_le,precision,
      Nat.clog_le_iff_le_pow (by decide : 1 < (2:ℕ)),Nat.ceil_le]
    rw [Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) (by positivity),Real.rpow_natCast]
    exact_mod_cast (Iff.rfl : (1/epsilon:ℚ) ≤ (2:ℚ)^n ↔ (1/epsilon:ℚ) ≤ (2:ℚ)^n)
  exact le_antisymm ((hequiv _).mp le_rfl) ((hequiv _).mpr le_rfl)

lemma allowance_eq (L d : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    allowance L d epsilon=CompanionTerminalParameters.allowance L d (epsilon:ℝ) := by
  rw [allowance,precision_eq epsilon he,CompanionTerminalParameters.allowance]

lemma coefficient_eq (L d : ℕ) (hd : 1 ≤ d) (epsilon : ℚ) (he : 0 < epsilon) :
    coefficient L d epsilon=CompanionTerminalParameters.coefficient L d (epsilon:ℝ) := by
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have heR : (epsilon:ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have ha : (CompanionTerminalParameters.allowance L d (epsilon:ℝ):ℝ) ≠ 0 := by
    exact_mod_cast (CompanionTerminalParameters.allowance_positive L d (epsilon:ℝ)).ne'
  have hratio : (4:ℝ)*CompanionTerminalParameters.allowance L d (epsilon:ℝ)/
      CompanionTerminalParameters.gamma L d (epsilon:ℝ)=
      ((2048:ℚ)*d*(allowance L d epsilon)^2/epsilon:ℚ) := by
    rw [allowance_eq L d epsilon he]
    simp only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow]
    unfold CompanionTerminalParameters.gamma
    field_simp [hdR,heR,ha]
    ring
  rw [CompanionTerminalParameters.coefficient,hratio,natCeil_ratCast]
  rfl

variable {I J : Type} [Fintype I] [Fintype J]

/-- The full product allowance is computed from the input capacities'
binary lengths, rather than supplied as a counting hypothesis. -/
def capacityBits (A : Instance I J) : ℕ :=
  ∑ a : I×J,(A.b a.1 a.2+1).size

lemma capacity_product_bound (A : Instance I J) :
    (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^capacityBits A := by
  calc
    _ ≤ ∏ a : I×J,2^(A.b a.1 a.2+1).size :=
      Finset.prod_le_prod (fun a _ => (Nat.lt_size_self (A.b a.1 a.2+1)).le)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

lemma small_product_bound (A : Instance I J) :
    (∏ a : SmallCell A,((A.b a.val.1 a.val.2:ℝ)+1)) ≤
      (2:ℝ)^capacityBits A := by
  have he := Fintype.prod_subtype_mul_prod_subtype
    (fun a : I×J => A.small a.1 a.2=true) (fun a => A.b a.1 a.2+1)
  have hr : 1 ≤ ∏ a : {a : I×J // ¬A.small a.1 a.2=true},(A.b a.val.1 a.val.2+1) := by
    apply Finset.one_le_prod
    intro a _
    omega
  have hs : (∏ a : SmallCell A,(A.b a.val.1 a.val.2+1)) ≤
      ∏ a : I×J,(A.b a.1 a.2+1) := by
    rw [←he]
    exact Nat.le_mul_of_pos_right _ (by omega)
  exact_mod_cast hs.trans (capacity_product_bound A)

lemma finalPhase_eq (A : Instance I J) (L : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    CompanionTerminalApplication.finalPhase A L (epsilon:ℝ)=
      rationalHeight A (coefficient L A.d epsilon) := by
  rw [CompanionTerminalApplication.finalPhase,←coefficient_eq L A.d A.hd epsilon he]
  rfl

lemma coefficient_pos (L d : ℕ) (hd : 1 ≤ d) (epsilon : ℚ) (he : 0 < epsilon) :
    0 < coefficient L d epsilon := by
  rw [coefficient_eq L d hd epsilon he]
  exact CompanionTerminalParameters.coefficient_positive L d (epsilon:ℝ) hd (by exact_mod_cast he)

end
end ContingencyTables.CountingTerminalSchedule

end OAI

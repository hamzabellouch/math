import OAI.NumberTheory.DirichletL.Moments.CommonRawScale

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonRawCost
open CenteredMomentCommonRawScale CenteredMomentAllocationCost CenteredMomentSourceLiveColumn
open CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

theorem frozen_normalized_cost (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O) (hC : C≠0)
    (hprod : finiteTupleProduct B=C) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P M : ι → ℝ) (hP : ∀ i,0<P i)
    (hν : ∀ i I,‖ν i I‖≤1) (hWnorm : ∀ i x,‖Wslot i x‖≤M i) (hM : ∀ i,1≤M i)
    (a b : ℝ) (ha : 0<a) (hW : ∀ i,Function.support (Wslot i)⊆Set.Icc a b) :
    ‖frozenCoefficient B C R ν Wslot P‖^2/rawReduction B P≤
      ((∏ i,M i)^2*(max 1 b)^Fintype.card ι)/(Ideal.absNorm C:ℝ) := by
  have hN : (0:ℝ)<Ideal.absNorm C := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  have hR := rawReduction_pos B hB P hP
  by_cases hz : frozenCoefficient B C R ν Wslot P=0
  · rw [hz,norm_zero,zero_pow (by decide : 2≠0),zero_div]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)) hN.le
  · have hm := frozenCoefficient_norm B C R ν Wslot P M hν hWnorm hM
    have hh := (actual_reduction_norm B hB C R hprod ν Wslot P hP a b ha hW hz).2
    have hi : (1:ℝ)/rawReduction B P≤(max 1 b)^Fintype.card ι/(Ideal.absNorm C:ℝ) := by
      apply (div_le_div_iff₀ hR hN).mpr
      simpa only [one_mul] using hh
    calc
      _ ≤ (∏ i,M i)^2/rawReduction B P :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hm _) hR.le
      _ = (∏ i,M i)^2*(1/rawReduction B P) := by ring
      _ ≤ (∏ i,M i)^2*((max 1 b)^Fintype.card ι/(Ideal.absNorm C:ℝ)) :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg _)
      _ = _ := by ring

end SevenEighths.CenteredMomentCommonRawCost

end

end OAI

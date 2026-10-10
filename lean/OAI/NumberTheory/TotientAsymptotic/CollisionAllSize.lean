import OAI.NumberTheory.TotientAsymptotic.CollisionHeadSize
import OAI.NumberTheory.TotientAsymptotic.NormalFactorBands
import OAI.NumberTheory.TotientAsymptotic.SurvivingBlockSize

namespace OAI

/-! Ford's small integer conditions at every first difference, including zero. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

theorem collision_small_factors_all : ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
    ∀ i p q : ℕ, i ≤ R x H → L x H < m x → p.Prime →
    ∀ η ξ : RemainderDatum (L x H), IsBasicRemainder x H η →
    wholeWitnessPrime p η i ≠ wholeWitnessPrime q ξ i → ∀ y : ℝ, 1 ≤ y →
    (witnessBlockValue p η i (collisionLastIndex x i) : ℝ) ≤ y → (i=0 → y=x) →
    (collisionResidual η i : ℝ) ≤ y^(1/100 : ℝ) ∧
    (collisionCanceledProduct p q η ξ i (collisionLastIndex x i) : ℝ) ≤ y^(1/10 : ℝ) := by
  filter_upwards [collision_small_factors,eventually_collision_indices,eventually_tail_cut_separated]
    with H hsmall hind hsep
  filter_upwards [hsmall,collision_head_small_factors H,
    m_tendsto.eventually (eventually_ge_atTop H)] with x hs hhead hm
  intro i p q hi hL hp η ξ hη hfirst y hy hsize hzero
  have hk := (hind x hm i hi).2.2
  have hsmall' : (collisionResidual η i : ℝ) ≤ y^(1/100 : ℝ) ∧
      (collisionCanceledProduct p q η ξ i (collisionLastIndex x i) : ℝ) ≤ y^(1/100 : ℝ) := by
    by_cases hz : i=0
    · have hyx := hzero hz
      subst i
      subst y
      exact hhead _ p q hL hk hp hfirst η ξ hη
    · have hip : 1 ≤ i := by omega
      have hiL : i+2 ≤ L x H := by unfold R L at *; omega
      have hpi := basic_remainder_prime_ge_three hη
        (Finset.mem_Icc.mpr ⟨hip,by omega⟩) (by omega)
      have hv := hsize
      rw [witnessBlockValue_positive (p := p) (k := collisionLastIndex x i) hη hL hip (Nat.le_add_right _ _) hk] at hv
      have hp1 : ((remainderPrime η i-1 : ℕ) : ℝ) ≤ y := by
        have hn := Nat.le_mul_of_pos_right (remainderPrime η i-1)
          (Nat.totient_pos.mpr (suffixPreimage_pos hη (i := i)))
        exact (show ((remainderPrime η i-1 : ℕ) : ℝ) ≤
          ((remainderPrime η i-1)*(suffixPreimage η i).totient : ℕ) by exact_mod_cast hn).trans hv
      exact hs i (collisionLastIndex x i) p q hip hi hiL hL (Nat.le_add_right _ _) hk
        η ξ hη hpi hfirst y hp1
  refine ⟨hsmall'.1,hsmall'.2.trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)

end TotientAsymptotic

end

end OAI

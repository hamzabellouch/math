import OAI.NumberTheory.Jacobsthal.Partitions.BoxHeightBudget

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosSourcePolynomial
open ErdosInverseBoxHeight

theorem sourceZ_ge_one {z : ℝ} (hL : 1 ≤ Real.log z) : 1 ≤ sourceZ z := by
  apply Real.one_le_exp_iff.mpr
  exact div_nonneg (zero_le_one.trans hL) (Real.log_nonneg hL)

theorem square_scale_of_root_height {z Sq R : ℝ} (hSq : 0 ≤ Sq) (hR : 1 ≤ R)
    (hL : 1 ≤ Real.log z) (hheight : 2*Sq*R^2*(sourceZ z)^20 ≤ z^3) : Sq ≤ z^3 := by
  have hR2 : 1 ≤ R^2 := one_le_pow₀ hR
  have hZ20 : 1 ≤ (sourceZ z)^20 := one_le_pow₀ (sourceZ_ge_one hL)
  have hm : 1 ≤ R^2*(sourceZ z)^20 := one_le_mul_of_one_le_of_one_le hR2 hZ20
  have hf : 1 ≤ 2*(R^2*(sourceZ z)^20) := by linarith
  calc
    Sq = Sq*1 := by ring
    _ ≤ Sq*(2*(R^2*(sourceZ z)^20)) := mul_le_mul_of_nonneg_left hf hSq
    _ = 2*Sq*R^2*(sourceZ z)^20 := by ring
    _ ≤ z^3 := hheight

theorem uniform_source_square_scale (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 2 ≤ z ∧ 1 ≤ Real.log z ∧ ∀ Sq R p q xi : ℝ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ Sq/q → Sq/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      1 ≤ R → R ≤ z^((1 : ℝ)/100) → 0 ≤ xi → xi ≤ 1 → Sq ≤ z^3 := by
  filter_upwards [uniform_box_height C hC,source_B_bounds,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_ge_atTop (2 : ℝ)] with z hheight hB hL hz
  refine ⟨hz,hL,?_⟩
  intro Sq R p q xi hp hq hpq hSqratio hinfl hR hRhi hxi0 hxi1
  have hSq : 0 ≤ Sq := hq.le.trans ((one_le_div hq).mp hSqratio)
  have hqz := source_cofactor_le_square hL hp hq.le hpq
  have hh := hheight.2 Sq R (sourceB z) xi q hSq (zero_le_one.trans hR)
    hB.2.1 hB.2.2 hxi0 hxi1 hq hqz hinfl hRhi
  exact square_scale_of_root_height hSq hR hL hh

end ErdosSourcePolynomial

end

end Erdos970

end OAI

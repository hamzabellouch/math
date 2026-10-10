import OAI.NumberTheory.Jacobsthal.Partitions.BoxHeightBudget

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxHeight
open ErdosInverseAlignment ErdosInversePrimeBin

theorem uniform_literal_source_list (C eta α c : ℝ)
    (hC : 0 ≤ C) (heta : 0 < eta) (hα : 0 < α) (hc : 0 < c) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ Sq R p q xi : ℝ, ∀ a : ℕ → ℤ,
      1 ≤ p → 0 < q → p*q ≤ (sourceY z : ℝ) →
      1 ≤ Sq/q → Sq/q ≤ (1+xi)^(C*Real.log (sourceB z)) →
      z^α ≤ R → R ≤ z^((1:ℝ)/100) → eta ≤ xi → xi ≤ 1 →
      (sourceRationalList (primeBin R xi) a Sq R (sourceZ z) c).card ≤ ⌈2/c^2⌉₊ := by
  have hbin := uniform_source_prime_bin_list (C:=3) heta hα (by norm_num) hc
  have hL := Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [uniform_box_height C hC,source_B_bounds,hbin,hL] with z hH hB hbin hL
  refine ⟨hH.1,?_⟩
  intro Sq R p q xi a hp hq hpq hSqratio hinfl hRlo hRhi hxi hxi1
  have hqSq : q ≤ Sq := (one_le_div hq).mp hSqratio
  have hSq : 0 ≤ Sq := hq.le.trans hqSq
  have hR : 0 ≤ R := (Real.rpow_nonneg (by linarith [hH.1] : 0 ≤ z) α).trans hRlo
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have hqz : q ≤ z^2 := source_cofactor_le_square hL hp hq.le hpq
  have hheight := hH.2 Sq R (sourceB z) xi q hSq hR hB.2.1 hB.2.2
    hxi0 hxi1 hq hqz hinfl hRhi
  apply hbin.2 R xi Sq (sourceZ z) a hRlo hxi hxi1 hSq
  norm_num at hheight ⊢
  exact hheight

end ErdosInverseBoxHeight

end

end Erdos970

end OAI

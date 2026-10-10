import OAI.Geometry.CylinderCovering.Rational.DomainArea
import OAI.Geometry.CylinderCovering.Rational.EnergyIntegral
import OAI.Geometry.CylinderCovering.Rational.CostExpansion

namespace OAI

open Set MeasureTheory

noncomputable section
namespace SlopeRational

theorem normalizedIntegral_area_bound {d ε q Q : ℝ}
    (hd : 0 < d) (hQ : 0 ≤ Q) (hε : 0 ≤ ε)
    (hεsmall : ε ≤ 1 / (4 * (1 + Q))) (hq : 0 ≤ q) (hqQ : q ≤ Q * ε ^ 2) :
    |(∫ z in labelDomain d ε q, 1 / Real.sqrt (1 + ε ^ 2 * energyDensity d z)) -
      ((1 / 8 : ℝ) + ε ^ 2 * (ceilingIntegral d - energyIntegral d) + q / 2)| ≤
        ((3 / 8 : ℝ) * (3 / 64 : ℝ) ^ 2 * (3 / 8 : ℝ) +
          (3 / 64 : ℝ) * (1 + Q) / 2 + (1 + Q) ^ 2) * ε ^ 4 := by
  have harea := DomainArea.labelDomain_area_estimates_small hd.le hQ hε hεsmall hq hqQ
  have hbase : labelDomain d 0 0 = baseDomain := DomainArea.unperturbed_domain d
  have hsub : baseDomain ⊆ labelDomain d ε q := by
    rw [← hbase]
    exact DomainArea.unperturbed_subset hd.le hq
  have hmeas : Measurable (energyDensity d) := by
    unfold energyDensity a b radius
    fun_prop
  have hadded : volume.real (labelDomain d ε q \ baseDomain) ≤ (1 + Q) * ε ^ 2 := by
    simpa only [hbase] using harea.2.2
  exact CylinderCovering.RationalCost.cost_expansion_bound
    (labelDomain_measurableSet d ε q) RationalEnergy.baseDomain_isCompact.measurableSet hsub
    (labelDomain_isCompact d ε q).measure_lt_top hmeas (by norm_num : (0 : ℝ) ≤ 3 / 64)
    (fun z hz => RationalEnergy.energyDensity_bounds hd hz.1)
    harea.1 hadded harea.2.1

end SlopeRational

end

end OAI

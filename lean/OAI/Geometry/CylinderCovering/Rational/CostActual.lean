import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions
import OAI.Geometry.CylinderCovering.Rational.EnergyIntegralDefinitions
import OAI.Geometry.CylinderCovering.Rational.CostExpansion
import OAI.Geometry.CylinderCovering.Rational.EnergyBounds
import OAI.Geometry.CylinderCovering.Rational.Domain
import OAI.Geometry.CylinderCovering.Rational.DomainArea

namespace OAI

open Set MeasureTheory Filter
open scoped Topology
noncomputable section

namespace SlopeRational

lemma cost_physicalScale_pos : 0 < physicalScale := by
  unfold physicalScale
  positivity

lemma cost_physicalScale_sq : physicalScale ^ 2 = 1 / 2 := by
  unfold physicalScale
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma cost_physicalWeight_eq_energy (d ε : ℝ) (z : Plane) :
    RuledApproximation.physicalWeight physicalScale (ε • field d z) =
      1 / Real.sqrt (1 + ε ^ 2 * energyDensity d z) := by
  change 1 / Real.sqrt (1 + (ε * a d (z 0) (z 1)) ^ 2 +
    physicalScale ^ 2 * (ε * b d (z 0) (z 1)) ^ 2) = _
  rw [cost_physicalScale_sq]
  congr 2
  unfold energyDensity
  ring

lemma cost_normalization (d ε q : ℝ) :
    weightedCost d ε q / physicalScale =
      ∫ z in labelDomain d ε q, 1 / Real.sqrt (1 + ε ^ 2 * energyDensity d z) := by
  unfold weightedCost
  rw [mul_div_cancel_left₀ _ cost_physicalScale_pos.ne']
  apply integral_congr_ae
  filter_upwards with z
  exact cost_physicalWeight_eq_energy d ε z

lemma cost_ceiling_nonneg {d : ℝ} (hd : 0 < d) (Y : ℝ) :
    0 ≤ ceilingPolynomial d Y := by
  unfold ceilingPolynomial ceilingCoefficient ceilingConstant ceilingQuadratic alpha
  positivity

lemma cost_baseDomain_subset {d ε q : ℝ} (hd : 0 < d) (hq : 0 ≤ q) :
    baseDomain ⊆ labelDomain d ε q := by
  intro z hz
  rcases hz with ⟨hw, ht⟩
  change 0 ≤ z 1 at ht
  refine ⟨hw, by linarith, ?_⟩
  have hp := cost_ceiling_nonneg hd (z 0)
  have hn := mul_nonneg (sq_nonneg ε) hp
  linarith

lemma cost_baseDomain_measurable : MeasurableSet baseDomain := by
  exact (wedge_isClosed.inter (isClosed_le (f := fun _ : Plane => (0 : ℝ))
    (g := fun z => z 1) (by fun_prop) (by fun_prop))).measurableSet

theorem cost_bound_from_domain_area {d ε q J K Q : ℝ}
    (hd : 0 < d) (hq0 : 0 ≤ q) (hQ : 0 ≤ Q) (hq : q ≤ Q * ε ^ 2)
    (heps : ε ^ 2 ≤ 1) (hK : 0 ≤ K)
    (hbase : volume.real baseDomain = 1 / 8)
    (harea : |volume.real (labelDomain d ε q) -
      (1 / 8 + ε ^ 2 * J + q / 2)| ≤ K * ε ^ 4) :
    |weightedCost d ε q / physicalScale -
      (1 / 8 + ε ^ 2 * (J - energyIntegral d) + q / 2)| ≤
      ((3 / 8) * (3 / 64) ^ 2 * (1 / 8 + (|J| + Q / 2 + K)) +
        (3 / 64) * (|J| + Q / 2 + K) / 2 + K) * ε ^ 4 := by
  rw [cost_normalization]
  apply CylinderCovering.RationalCost.cost_expansion_bound_of_area
    (labelDomain_measurableSet d ε q) cost_baseDomain_measurable
    (cost_baseDomain_subset hd hq0)
    (labelDomain_isCompact d ε q).measure_lt_top
    (rational_energy_measurable d) (by norm_num)
    (fun z hz => rational_energy_bounds hd hz.1) hbase heps hK hQ hq harea

theorem weightedCost_expansion_bound {d ε q Q : ℝ}
    (hd : 0 < d) (hQ : 0 ≤ Q) (hε : 0 ≤ ε)
    (hsmall : ε ≤ 1 / (4 * (1 + Q))) (hq0 : 0 ≤ q) (hqQ : q ≤ Q * ε ^ 2) :
    |weightedCost d ε q / physicalScale -
      (1 / 8 + ε ^ 2 * (ceilingIntegral d - energyIntegral d) + q / 2)| ≤
      ((3 / 8) * (3 / 64) ^ 2 * (3 / 8) +
        (3 / 64) * (1 + Q) / 2 + (1 + Q) ^ 2) * ε ^ 4 := by
  obtain ⟨harea, hvol, hadd⟩ :=
    DomainArea.labelDomain_area_estimates_small hd.le hQ hε hsmall hq0 hqQ
  have heq : labelDomain d 0 0 = baseDomain := DomainArea.unperturbed_domain d
  rw [heq] at hadd
  rw [cost_normalization]
  exact CylinderCovering.RationalCost.cost_expansion_bound
    (labelDomain_measurableSet d ε q) cost_baseDomain_measurable
    (cost_baseDomain_subset hd hq0)
    (labelDomain_isCompact d ε q).measure_lt_top
    (rational_energy_measurable d) (by norm_num)
    (fun z hz => rational_energy_bounds hd hz.1) harea hadd hvol

theorem weightedCost_expansion {d : ℝ} (hd : 0 < d) {q : ℝ → ℝ}
    (hq0 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 ≤ q ε)
    (hq : Asymptotics.IsBigO (𝓝[>] (0 : ℝ)) q (fun ε => ε ^ 2)) :
    Asymptotics.IsBigO (𝓝[>] (0 : ℝ))
      (fun ε => weightedCost d ε (q ε) / physicalScale -
        (1 / 8 + ε ^ 2 * (ceilingIntegral d - energyIntegral d) + q ε / 2))
      (fun ε => ε ^ 4) := by
  obtain ⟨Q, hQ, hb⟩ := hq.exists_pos
  apply Asymptotics.IsBigO.of_bound
    ((3 / 8) * (3 / 64) ^ 2 * (3 / 8) + (3 / 64) * (1 + Q) / 2 + (1 + Q) ^ 2)
  have hδ : 0 < 1 / (4 * (1 + Q)) := by positivity
  have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  filter_upwards [hq0, hb.bound, self_mem_nhdsWithin,
    ht.eventually (gt_mem_nhds hδ)] with ε heq heB hepos heδ
  have heB' : q ε ≤ Q * ε ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg heq, abs_of_nonneg (sq_nonneg ε)] using heB
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ ε ^ 4 by positivity)] using
    weightedCost_expansion_bound hd hQ.le hepos.le heδ.le heq heB'

end SlopeRational

end

end OAI

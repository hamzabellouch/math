import OAI.Geometry.CylinderCovering.Rational.ConstructionDefinitions
import OAI.Geometry.CylinderCovering.Rational.Realization
import OAI.Geometry.CylinderCovering.Rational.Asymptotic
import OAI.Geometry.CylinderCovering.Rational.Gap

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace CylinderCovering

theorem minimumShadowArea_le_shadowArea (K : Set Space) {u : Space}
    (hu : ‖u‖ = 1) : minimumShadowArea K ≤ shadowArea K u := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro a ⟨v, hv, rfl⟩
    exact ENNReal.toReal_nonneg
  · exact ⟨u, hu, rfl⟩

theorem relativeCost_le_familyArea_div_minimum {K : Set Space}
    (hK : 0 < minimumShadowArea K) {n : ℕ}
    (C : Fin n → RuledApproximation.Cylinder) :
    relativeCost K C ≤ RuledApproximation.familyArea C / minimumShadowArea K := by
  rw [relativeCost, RuledApproximation.familyArea, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg hK
    (minimumShadowArea_le_shadowArea K (C i).unit_axis)

end CylinderCovering

namespace SlopeRational

theorem finite_sweeps_separate {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hsmall : ε < 8 * d) (q : ℝ) {e : ℝ} (he : 0 < e) :
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.parallelogram
      (lowerSweep d ε q) (weightedCost d ε q + e) ∧
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.parallelogram
      (upperSweep d ε q) (weightedCost d ε q + e) := by
  obtain ⟨U, hU, hDU, hreg⟩ := field_smoothNear_labelDomain hd ε q
  have hsmooth : RuledApproximation.SmoothNear 1 (labelDomain d ε q) (field d) :=
    ⟨U, hU, hDU, hreg.of_le (by norm_num)⟩
  have hplus : ∀ p ∈ labelDomain d ε q,
      RuledApproximation.HyperbolicAt (1 / 2) (fun z => ε • field d z) p := by
    intro p hp
    exact rational_hyperbolic hd hε.ne' (by simpa [abs_of_pos hε] using hsmall) hp
  have hminus : ∀ p ∈ labelDomain d ε q,
      RuledApproximation.HyperbolicAt (1 / 2) (fun z => -ε • field d z) p := by
    intro p hp
    exact rational_hyperbolic hd (neg_ne_zero.mpr hε.ne')
      (by simpa [abs_of_pos hε] using hsmall) hp
  have hp := RuledApproximation.physical_hyperbolic_cover physicalScale_pos
    (by norm_num : (0 : ℝ) < 1 / 2) (labelDomain_isCompact d ε q)
    (smoothNear_const_smul hsmooth ε) hplus he
  have hm := RuledApproximation.physicalHyperbolic physicalScale (1 / 2)
    (labelDomain d ε q) (fun p => -ε • field d p) physicalScale_pos
    (by norm_num) (labelDomain_isCompact d ε q) (smoothNear_const_smul hsmooth (-ε))
    hminus e he reflectionIsometry.toIsometryEquiv
  have hweight (p : Plane) :
      RuledApproximation.physicalWeight physicalScale (-ε • field d p) =
        RuledApproximation.physicalWeight physicalScale (ε • field d p) := by
    rw [neg_smul, RuledApproximation.physicalWeight_neg]
  simp_rw [hweight] at hm
  exact ⟨hp, hm⟩

theorem strict_finite_cover_of_coverage_cost
    (hmin : CylinderCovering.minimumShadowArea referenceTetrahedron = physicalScale / 2)
    {d ε q : ℝ} (hd : 0 < d) (hε : 0 < ε) (hsmall : ε < 8 * d)
    (hcoverage : referenceTetrahedron ⊆ lowerSweep d ε q ∪ upperSweep d ε q)
    (hcost : weightedCost d ε q < physicalScale / 8) :
    HasStrictFiniteCover d ε q := by
  let e := (physicalScale / 4 - 2 * weightedCost d ε q) / 4
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨⟨n, C, hC, hCcov, hCa⟩, ⟨m, D, hD, hDcov, hDa⟩⟩ :=
    finite_sweeps_separate hd hε hsmall q he
  have harea : RuledApproximation.familyArea C + RuledApproximation.familyArea D <
      physicalScale / 4 := by dsimp [e] at hCa hDa; linarith
  refine ⟨n, m, C, D, hC, hD, hCcov, hDcov,
    hcoverage.trans (union_subset_union hCcov hDcov), harea, ?_⟩
  have hmpos : 0 < CylinderCovering.minimumShadowArea referenceTetrahedron := by
    rw [hmin]; exact half_pos physicalScale_pos
  have hrelC := CylinderCovering.relativeCost_le_familyArea_div_minimum hmpos C
  have hrelD := CylinderCovering.relativeCost_le_familyArea_div_minimum hmpos D
  rw [hmin] at hrelC hrelD
  have hrel := add_le_add hrelC hrelD
  rw [← add_div] at hrel
  apply hrel.trans_lt
  apply (div_lt_iff₀ (half_pos physicalScale_pos)).2
  linarith

theorem eventually_strict_finite_cover
    (hmin : CylinderCovering.minimumShadowArea referenceTetrahedron = physicalScale / 2)
    {d : ℝ} (hd : 0 < d) {q : ℝ → ℝ}
    (hcov : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      referenceTetrahedron ⊆ lowerSweep d ε (q ε) ∪ upperSweep d ε (q ε))
    (hcost : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      weightedCost d ε (q ε) / physicalScale < 1 / 8) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      weightedCost d ε (q ε) < physicalScale / 8 ∧ HasStrictFiniteCover d ε (q ε) := by
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 8 * d :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 8 * d by positivity))
  filter_upwards [hcov, hcost, hsmall, self_mem_nhdsWithin] with ε hc hk hs he
  have hcost' : weightedCost d ε (q ε) < physicalScale / 8 := by
    have h := (div_lt_iff₀ physicalScale_pos).1 hk
    linarith
  exact ⟨hcost', strict_finite_cover_of_coverage_cost hmin hd he hs hc hcost'⟩

theorem paddingSchedules_of_asymptotic
    (hmin : CylinderCovering.minimumShadowArea referenceTetrahedron = physicalScale / 2)
    (hasym : AsymptoticStatement) : PaddingSchedulesStatement := by
  constructor
  · obtain ⟨d, hd, hg⟩ := exists_positive_coefficientGap
    exact ⟨d, hd, sub_pos.mpr hg⟩
  · intro d hd hg
    constructor
    · have hq : AdmissiblePadding (fun ε : ℝ => ε ^ (5 / 2 : ℝ)) :=
        ⟨vanishing_padding_conditions.1, vanishing_padding_conditions.2.1,
          vanishing_padding_conditions.2.2.1⟩
      obtain ⟨hc, hk⟩ := hasym.1 d hd _ hq
      have hg' : ceilingIntegral d < energyIntegral d := sub_pos.mp hg
      exact eventually_strict_finite_cover hmin hd hc (vanishing_padding_cost_lt hg' hk)
    · intro η hη hηg
      have hq : AdmissiblePadding (fun ε : ℝ => η * ε ^ 2) := quadratic_padding_conditions hη
      obtain ⟨hc, hk⟩ := hasym.1 d hd _ hq
      have hgap : ceilingIntegral d - energyIntegral d + η / 2 < 0 := by
        unfold coefficientGap at hηg
        linarith
      exact eventually_strict_finite_cover hmin hd hc (quadratic_padding_cost_lt hgap hk)

end SlopeRational

end

end OAI

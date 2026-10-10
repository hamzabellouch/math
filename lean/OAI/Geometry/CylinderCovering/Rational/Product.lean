import OAI.Geometry.CylinderCovering.Rational.ProductDefinitions
import OAI.Geometry.CylinderCovering.Rational.Construction
import OAI.Geometry.CylinderCovering.Ruled.Similarity

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace SlopeRational

theorem open_cover_reflection {S : Set Space} {A : ℝ}
    (h : RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.openBounded S A) :
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.openBounded
      (reflection '' S) A := by
  have ht := h.openBounded_similarity (0 : Space) (r := 1) (by norm_num)
    reflectionIsometry
  have hmap : CylinderCovering.Similarity.map (0 : Space) 1 reflectionIsometry =
      reflection := by
    funext x
    simp only [CylinderCovering.Similarity.map, one_smul, zero_add]
    rfl
  rw [hmap] at ht
  simpa only [one_pow, one_mul] using ht

theorem product_finite_sweeps_separate {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hsmall : ε < 8 * d) (q : ℝ) {e : ℝ} (he : 0 < e) :
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.openBounded
      (lowerSweep d ε q) (weightedCost d ε q + e) ∧
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.openBounded
      (upperSweep d ε q) (weightedCost d ε q + e) := by
  obtain ⟨hD, hfrontier, ⟨U, hU, hDU, hreg⟩, hplus, hminus⟩ :=
    rational_approximation_eligibility hd hε hsmall q
  have hsmooth : RuledApproximation.SmoothNear 1 (labelDomain d ε q) (field d) :=
    ⟨U, hU, hDU, hreg.of_le (by norm_num)⟩
  have hp := RuledApproximation.productCell physicalScale (1 / 2)
    (labelDomain d ε q) (fun p => ε • field d p) physicalScale_pos
    (by norm_num) hD hfrontier (smoothNear_const_smul hsmooth ε) hplus e he
  have hm := RuledApproximation.productCell physicalScale (1 / 2)
    (labelDomain d ε q) (fun p => -ε • field d p) physicalScale_pos
    (by norm_num) hD hfrontier (smoothNear_const_smul hsmooth (-ε)) hminus e he
  have hweight (p : Plane) :
      RuledApproximation.physicalWeight physicalScale (-ε • field d p) =
        RuledApproximation.physicalWeight physicalScale (ε • field d p) := by
    rw [neg_smul, RuledApproximation.physicalWeight_neg]
  simp_rw [hweight] at hm
  exact ⟨hp, open_cover_reflection hm⟩

theorem product_finite_sweeps {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hsmall : ε < 8 * d) (q : ℝ) {e : ℝ} (he : 0 < e) :
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.openBounded
      (lowerSweep d ε q ∪ upperSweep d ε q) (2 * weightedCost d ε q + e) := by
  obtain ⟨hp, hm⟩ := product_finite_sweeps_separate hd hε hsmall q (half_pos he)
  convert hp.union hm using 1
  ring

theorem product_strict_cover_of_coverage_cost {d ε q : ℝ}
    (hd : 0 < d) (hε : 0 < ε) (hsmall : ε < 8 * d)
    (hcoverage : referenceTetrahedron ⊆ lowerSweep d ε q ∪ upperSweep d ε q)
    (hcost : weightedCost d ε q < physicalScale / 8) :
    HasStrictOpenFiniteCover d ε q := by
  let e := (physicalScale / 4 - 2 * weightedCost d ε q) / 4
  have he : 0 < e := by dsimp [e]; linarith
  obtain ⟨⟨n, C, hC, hCcov, hCa⟩, ⟨m, D, hD, hDcov, hDa⟩⟩ :=
    product_finite_sweeps_separate hd hε hsmall q he
  have harea : RuledApproximation.familyArea C + RuledApproximation.familyArea D <
      physicalScale / 4 := by dsimp [e] at hCa hDa; linarith
  refine ⟨n, m, C, D, hC, hD, hCcov, hDcov,
    hcoverage.trans (union_subset_union hCcov hDcov), harea, ?_⟩
  have hmpos : 0 < CylinderCovering.minimumShadowArea referenceTetrahedron := by
    rw [referenceTetrahedron_minimumShadowArea]
    exact half_pos physicalScale_pos
  have hrelC := CylinderCovering.relativeCost_le_familyArea_div_minimum hmpos C
  have hrelD := CylinderCovering.relativeCost_le_familyArea_div_minimum hmpos D
  rw [referenceTetrahedron_minimumShadowArea] at hrelC hrelD
  have hrel := add_le_add hrelC hrelD
  rw [← add_div] at hrel
  apply hrel.trans_lt
  apply (div_lt_iff₀ (half_pos physicalScale_pos)).2
  linarith

theorem product_fractional_eventually {d : ℝ} (hd : 0 < d)
    (hgap : 0 < coefficientGap d) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      weightedCost d ε (ε ^ (5 / 2 : ℝ)) < physicalScale / 8 ∧
      HasStrictOpenFiniteCover d ε (ε ^ (5 / 2 : ℝ)) := by
  have hq : AdmissiblePadding (fun ε : ℝ => ε ^ (5 / 2 : ℝ)) :=
    ⟨vanishing_padding_conditions.1, vanishing_padding_conditions.2.1,
      vanishing_padding_conditions.2.2.1⟩
  obtain ⟨hc, hk⟩ := asymptotic_main.1 d hd _ hq
  have hcost := vanishing_padding_cost_lt (sub_pos.mp hgap) hk
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 8 * d :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 8 * d by positivity))
  filter_upwards [hc, hcost, hsmall, self_mem_nhdsWithin] with ε hcov hcost hs he
  have hcost' : weightedCost d ε (ε ^ (5 / 2 : ℝ)) < physicalScale / 8 := by
    have h := (div_lt_iff₀ physicalScale_pos).1 hcost
    linarith
  exact ⟨hcost', product_strict_cover_of_coverage_cost hd he hs hcov hcost'⟩

theorem product_approximation : ProductApproximationStatement := by
  intro d ε hd hε hs q e he
  exact product_finite_sweeps_separate hd hε hs q he

theorem product_fractional : ProductFractionalStatement := by
  refine ⟨?_, fun d hd hg => product_fractional_eventually hd hg⟩
  obtain ⟨d, hd, hg⟩ := exists_positive_coefficientGap
  exact ⟨d, hd, sub_pos.mpr hg⟩

theorem product_realization : ProductRealizationStatement :=
  ⟨product_approximation, product_fractional⟩

end SlopeRational

end

end OAI

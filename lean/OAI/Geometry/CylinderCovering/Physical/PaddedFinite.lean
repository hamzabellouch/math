import OAI.Geometry.CylinderCovering.Physical.PaddedFiniteDefinitions
import OAI.Geometry.CylinderCovering.Physical.CapNormalized
import OAI.Geometry.CylinderCovering.Physical.PaddedCosts

namespace OAI

open Set Filter
open scoped Topology
noncomputable section
namespace RadialPhysical
open CylinderCovering

lemma paddedNumerator_continuous (fractional : Bool) (b eta c : ℝ) :
    Continuous (paddedNumerator fractional b eta c) := by
  unfold paddedNumerator
  fun_prop

lemma physicalPaddedCap_continuous (centered fractional : Bool) (b eta c : ℝ) :
    Continuous (physicalPaddedCap centered fractional b eta c) := by
  cases centered
  · exact (paddedNumerator_continuous fractional b eta c).div_const 2
  · exact paddedNumerator_continuous fractional b eta c

lemma paddedNumerator_nonneg (fractional : Bool) (b eta c s : ℝ)
    (heta : 0 ≤ eta) (hc : 0 ≤ c) :
    0 ≤ paddedNumerator fractional b eta c s := by
  cases fractional <;> simp only [paddedNumerator, Bool.false_eq_true, ite_false, ite_true]
  · positivity
  · positivity

lemma physicalPaddedCap_nonneg (centered fractional : Bool) (b eta c s : ℝ)
    (heta : 0 ≤ eta) (hc : 0 ≤ c) :
    0 ≤ physicalPaddedCap centered fractional b eta c s := by
  cases centered
  · exact div_nonneg (paddedNumerator_nonneg fractional b eta c s heta hc) (by norm_num)
  · exact paddedNumerator_nonneg fractional b eta c s heta hc

private theorem padded_coverage_of_canonical (centered fractional : Bool)
    {b : ℝ} (hb : 0 < b) (eta c : ℝ)
    (hcover : RadialPairedSweep.tetrahedron (Real.sqrt 2) ⊆
      RadialPairedSweep.upperSweep (Real.sqrt 2) (effectiveTilt b eta)
        (fun r => paddedNumerator fractional b eta c (b*r)) ∪
      RadialPairedSweep.lowerSweep (Real.sqrt 2) (effectiveTilt b eta)
        (fun r => paddedNumerator fractional b eta c (b*r))) :
    modelBody centered b ⊆
      upperSweepOn centered b eta (physicalPaddedCap centered fractional b eta c) (Icc (-b) b) ∪
      lowerSweepOn centered b eta (physicalPaddedCap centered fractional b eta c) (Icc (-b) b) := by
  cases centered
  · apply halfheight_coverage_of_canonical hb
    have hp : (fun r => 2*physicalPaddedCap false fractional b eta c (b*r)) =
        fun r => paddedNumerator fractional b eta c (b*r) := by
      funext r
      simp only [physicalPaddedCap, Bool.false_eq_true, ite_false]
      ring
    rw [hp]
    exact hcover
  · exact centered_coverage_of_canonical hb eta _ hcover

theorem physicalPadded_cubic_covers (centered : Bool) {b eta c : ℝ}
    (hb : 0 < b) (heta : 0 < eta) (hc : (9/2 : ℝ)*b^6 ≤ c) :
    modelBody centered b ⊆
      upperSweepOn centered b eta (physicalPaddedCap centered false b eta c) (Icc (-b) b) ∪
      lowerSweepOn centered b eta (physicalPaddedCap centered false b eta c) (Icc (-b) b) := by
  apply padded_coverage_of_canonical centered false hb
  simp only [paddedNumerator, Bool.false_eq_true, ite_false]
  rw [centered_cubic_cap_profile hb]
  exact RadialCapCoverage.cubic_covers
    ((le_div_iff₀ (pow_pos hb 6)).mpr hc) (mul_pos heta (sq_pos_of_pos hb))

theorem physicalPadded_fractional_covers (centered : Bool) {b eta c : ℝ}
    (hb : 0 < b) (heta : 0 < eta) (hc : 0 < c)
    (hsmall : eta*b^2 ≤ (2*(c/b^5)/9)^2) :
    modelBody centered b ⊆
      upperSweepOn centered b eta (physicalPaddedCap centered true b eta c) (Icc (-b) b) ∪
      lowerSweepOn centered b eta (physicalPaddedCap centered true b eta c) (Icc (-b) b) := by
  apply padded_coverage_of_canonical centered true hb
  simp only [paddedNumerator, ite_true]
  rw [centered_fractional_cap_profile hb heta]
  exact RadialCapCoverage.fractional_covers (div_pos hc (pow_pos hb 5))
    (mul_pos heta (sq_pos_of_pos hb)) hsmall

private theorem padded_finite_of_cover (centered fractional : Bool) {b eta c : ℝ}
    (hb : 0 < b) (heta : 0 ≤ eta) (hc : 0 ≤ c)
    (hcover : modelBody centered b ⊆
      upperSweepOn centered b eta (physicalPaddedCap centered fractional b eta c) (Icc (-b) b) ∪
      lowerSweepOn centered b eta (physicalPaddedCap centered fractional b eta c) (Icc (-b) b)) :
    PaddedFiniteAt centered fractional b eta c := by
  intro tagU tagL htagU htagL
  exact physical_family_of_sweep_cover centered b eta hb
    (physicalPaddedCap centered fractional b eta c)
    (physicalPaddedCap_continuous centered fractional b eta c).continuousOn
    (fun s _ => physicalPaddedCap_nonneg centered fractional b eta c s heta hc)
    hcover tagU tagL htagU htagL

theorem physicalPadded_cubic_finite (centered : Bool) {b eta c : ℝ}
    (hb : 0 < b) (heta : 0 < eta) (hc : (9/2 : ℝ)*b^6 ≤ c) :
    PaddedFiniteAt centered false b eta c := by
  apply padded_finite_of_cover centered false hb heta.le
  · exact le_trans (by positivity) hc
  · exact physicalPadded_cubic_covers centered hb heta hc

theorem physicalPadded_fractional_finite (centered : Bool) {b eta c : ℝ}
    (hb : 0 < b) (heta : 0 < eta) (hc : 0 < c)
    (hsmall : eta*b^2 ≤ (2*(c/b^5)/9)^2) :
    PaddedFiniteAt centered true b eta c := by
  exact padded_finite_of_cover centered true hb heta.le hc.le
    (physicalPadded_fractional_covers centered hb heta hc hsmall)

theorem eventually_physicalPadded_finite (centered fractional : Bool) {b c : ℝ}
    (hb : 0 < b) (hc : if fractional then 0 < c else (9/2 : ℝ)*b^6 ≤ c) :
    ∀ᶠ eta : ℝ in 𝓝[>] 0, PaddedFiniteAt centered fractional b eta c := by
  cases fractional
  · simp only [Bool.false_eq_true, ite_false] at hc
    filter_upwards [eventually_mem_nhdsWithin] with eta heta
    exact physicalPadded_cubic_finite centered hb heta hc
  · simp only [ite_true] at hc
    have hdelta : 0 < ((2*(c/b^5)/9)^2)/b^2 := by positivity
    filter_upwards [Ioo_mem_nhdsGT hdelta] with eta heta
    exact physicalPadded_fractional_finite centered hb heta.1 hc
      ((lt_div_iff₀ (sq_pos_of_pos hb)).mp heta.2).le

lemma scaledCost_halve (b eta : ℝ) (T : ℝ → ℝ) :
    scaledCost b eta (fun s => T s/2) = scaledCost b eta T/4 := by
  unfold scaledCost
  have hd : (fun s => scaledDensity b eta (fun s => T s/2) s) =
      fun s => (1/4 : ℝ)*scaledDensity b eta T s := by
    funext s
    unfold scaledDensity
    ring
  rw [hd, intervalIntegral.integral_const_mul]
  ring

private theorem padded_strict_of_cost (centered fractional : Bool) (b eta c : ℝ)
    (hfinite : PaddedFiniteAt centered fractional b eta c)
    (hcost : scaledCost b eta (physicalPaddedCap centered fractional b eta c) <
      physicalHalfReference centered b) :
    PaddedStrictFiniteAt centered fractional b eta c := by
  intro tagU tagL htagU htagL
  obtain ⟨C, hC⟩ := hfinite tagU tagL htagU htagL
  exact ⟨C, hC, hC.eventually_strict hcost⟩

private theorem padded_normalized_of_cost (centered fractional : Bool) {b : ℝ}
    (hb : 0 < b) (eta c : ℝ)
    (hfinite : PaddedFiniteAt centered fractional b eta c)
    (hcost : scaledCost b eta (physicalPaddedCap centered fractional b eta c) <
      physicalHalfReference centered b) :
    PaddedNormalizedFiniteAt centered fractional b eta c := by
  intro tagU tagL htagU htagL
  obtain ⟨C, hC⟩ := hfinite tagU tagL htagU htagL
  exact ⟨C, hC, hC.eventually_both_half_bounds hb hcost⟩

theorem eventually_physicalPadded_strict (centered fractional : Bool) {b c : ℝ}
    (hb : 0 < b) (hc : 0 ≤ c) :
    ∀ᶠ eta : ℝ in 𝓝[>] 0,
      scaledCost b eta (physicalPaddedCap centered fractional b eta c) <
        physicalHalfReference centered b := by
  have hcenter : ∀ᶠ eta : ℝ in 𝓝[>] 0,
      scaledCost b eta (paddedNumerator fractional b eta c) < 2*b*height b := by
    cases fractional
    · exact centered_cubic_cost_strict hb hc
    · exact centered_fractional_cost_strict hb hc
  cases centered
  · filter_upwards [hcenter] with eta heta
    change scaledCost b eta (fun s => paddedNumerator fractional b eta c s/2) <
      b*height b/2
    rw [scaledCost_halve]
    linarith
  · exact hcenter

theorem physical_padded_finite : PhysicalPaddedFiniteStatement := by
  refine {
    cubic_all := fun centered b c hb hc eta heta =>
      physicalPadded_cubic_finite centered hb heta hc
    fractional_threshold := fun centered b c hb hc eta heta hsmall =>
      physicalPadded_fractional_finite centered hb heta hc hsmall
    eventual_strict := ?_
    eventual_normalized := ?_ }
  · intro centered fractional b c hb hc
    have hc0 : 0 ≤ c := by
      cases fractional
      · exact le_trans (by positivity) hc
      · exact le_of_lt hc
    filter_upwards [eventually_physicalPadded_finite centered fractional hb hc,
      eventually_physicalPadded_strict centered fractional hb hc0] with eta hfinite hcost
    exact padded_strict_of_cost centered fractional b eta c hfinite hcost
  · intro centered fractional b c hb hc
    have hc0 : 0 ≤ c := by
      cases fractional
      · exact le_trans (by positivity) hc
      · exact le_of_lt hc
    filter_upwards [eventually_physicalPadded_finite centered fractional hb hc,
      eventually_physicalPadded_strict centered fractional hb hc0] with eta hfinite hcost
    exact padded_normalized_of_cost centered fractional hb eta c hfinite hcost

end RadialPhysical

end

end OAI

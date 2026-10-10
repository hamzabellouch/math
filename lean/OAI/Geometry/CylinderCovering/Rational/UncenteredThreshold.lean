import OAI.Geometry.CylinderCovering.Rational.UncenteredThresholdDefinitions
import OAI.Geometry.CylinderCovering.Rational.DictionaryBridge
import OAI.Geometry.CylinderCovering.Rational.RationalThreshold

namespace OAI

noncomputable section
open Set
namespace RationalDictionary

theorem threshold_coordinate_identity {d0 : ℝ} (hd : 0 < d0) (k r u : ℝ) :
    SlopeRational.threshold (centeredRegularization d0) (centeredTilt d0 k)
      (-ell * r) (ell * u) = (1 - threshold d0 k r u) / 2 := by
  have hd' : 1 + d0 ≠ 0 := by linarith
  have ha : SlopeRational.a (d0 / 2) (ell * u) 0 =
      -SlopeRational.ceilingCoefficient (d0 / 2) (ell * u) := by
    unfold SlopeRational.a SlopeRational.radius SlopeRational.ceilingCoefficient
      SlopeRational.ceilingConstant SlopeRational.ceilingQuadratic
    ring
  have hv := v1_dictionary (s := 1) hd' u
  simp only [sub_self, zero_div] at hv
  rw [ha] at hv
  have hc : SlopeRational.ceilingCoefficient (d0 / 2) (ell * u) =
      v1 d0 u 1 / (4 * (1 + d0)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hd')).mpr
    nlinarith only [hv]
  unfold SlopeRational.threshold centeredRegularization
  rw [ceiling_dictionary hd', hc]
  unfold SlopeRational.alpha centeredTilt threshold
  have h₁ : 1 + 2 * (d0 / 2) = 1 + d0 := by ring
  rw [h₁]
  field_simp
  ring_nf
  rw [ell_sq]
  ring

theorem labelMap_lineMap {d0 k r : ℝ} {p : Plane} (hs : p 1 + d0 ≠ 0) :
    labelMap (lineMap d0 k r p) =
      SlopeRational.tiltedMap (centeredRegularization d0)
        (centeredTilt d0 k * (-ell * r)) (labelMap p) := by
  have h := first_point_dictionary hs k r (p 0)
  apply PiLp.ext
  intro i
  fin_cases i
  · have h₀ := congrArg (fun z : Space => z 1) h
    exact h₀
  · have h₁ := congrArg (fun z : Space => z 2) h
    change ell * (1 - (p 1 + r * k * v2 d0 (p 0) (p 1))) =
      c0 * ((1 - p 1) / 2 + centeredTilt d0 k * (-ell * r) *
        SlopeRational.b (d0 / 2) (ell * p 0) ((1 - p 1) / 2)) at h₁
    change (1 - (p 1 + r * k * v2 d0 (p 0) (p 1))) / 2 =
      (1 - p 1) / 2 + centeredTilt d0 k * (-ell * r) *
        SlopeRational.b (d0 / 2) (ell * p 0) ((1 - p 1) / 2)
    nth_rw 1 [ell_eq_half_c0] at h₁
    nlinarith [c0_pos]

theorem uncentered_threshold_quantitative {d0 : ℝ} (hd : 0 < d0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ k eta0 r u z : ℝ, 0 < k → k < δ → C * k ≤ eta0 →
        |r| ≤ 2 * c0 → 0 ≤ z → z ≤ 2 → |u| ≤ c0 * z →
        z ≤ threshold d0 k r u →
        ∃ p ∈ uncenteredDomain d0 eta0 k, lineMap d0 k r p = vec2 u z := by
  obtain ⟨δ, C, hδ, hC, hinc⟩ :=
    SlopeRational.thresholdInclusion_main (d0 / 2) (by positivity)
  let K : ℝ := 4 * (1 + d0)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨δ / K, 2 * C * K ^ 3, div_pos hδ hK, by positivity, ?_⟩
  intro k eta0 r u z hk hsmall hpadding hr hz₀ hz₂ hu hthreshold
  have he : 0 < centeredTilt d0 k := mul_pos hK hk
  have hesmall : centeredTilt d0 k < δ := by
    have hh := (lt_div_iff₀ hK).mp hsmall
    change K * k < δ
    nlinarith only [hh]
  have hq : C * centeredTilt d0 k ^ 3 ≤ centeredPadding eta0 k := by
    have hh := mul_le_mul_of_nonneg_right hpadding (sq_nonneg k)
    change C * (K * k) ^ 3 ≤ eta0 * k ^ 2 / 2
    nlinarith only [hh]
  have hx : |-ell * r| ≤ 1 / 2 := by
    simpa only [neg_mul, abs_neg] using (free_coordinate_iff r).mpr hr
  have hu' : |u| ≤ 2 * c0 := by nlinarith [c0_pos]
  have hy : |ell * u| ≤ 1 / 2 := (free_coordinate_iff u).mpr hu'
  have ht : |(1 - z) / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hw : SlopeRational.vec2 (ell * u) ((1 - z) / 2) ∈ SlopeRational.wedge :=
    (wedge_iff u z).mp hu
  have hθ : SlopeRational.threshold (d0 / 2) (centeredTilt d0 k)
      (-ell * r) (ell * u) ≤ (1 - z) / 2 := by
    rw [show d0 / 2 = centeredRegularization d0 from rfl,
      threshold_coordinate_identity hd]
    linarith
  obtain ⟨q, hqdom, hqmap⟩ := hinc (centeredTilt d0 k) (centeredPadding eta0 k)
    (-ell * r) (ell * u) ((1 - z) / 2) he hesmall hq hx hy ht hw hθ
  let p := inverseLabelMap q
  have hp : p ∈ uncenteredDomain d0 eta0 k := by
    apply (labelDomain_iff hd eta0 k p).mpr
    simpa [p, centeredRegularization] using hqdom
  refine ⟨p, hp, ?_⟩
  apply labelMap_injective
  rw [labelMap_lineMap (ne_of_gt (add_pos_of_nonneg_of_pos hp.1 hd))]
  have hl : labelMap p = q := labelMap_inverseLabelMap q
  rw [hl]
  exact hqmap

theorem uncentered_threshold : UncenteredThresholdStatement := by
  intro d0 eta0 hd heta
  obtain ⟨δ, C, hδ, hC, hinc⟩ := uncentered_threshold_quantitative hd
  refine ⟨min δ (eta0 / C), lt_min hδ (div_pos heta hC), ?_⟩
  intro k r u z hk hsmall hr hz₀ hz₂ hu hthreshold
  apply hinc k eta0 r u z hk (hsmall.trans_le (min_le_left _ _)) _ hr hz₀ hz₂ hu hthreshold
  have hh := (lt_div_iff₀ hC).mp (hsmall.trans_le (min_le_right _ _))
  nlinarith only [hh]

theorem uncentered_paired_coverage : UncenteredCoverageStatement := by
  intro d0 eta0 hd heta
  obtain ⟨δ, hδ, hinc⟩ := uncentered_threshold d0 eta0 hd heta
  refine ⟨δ, hδ, ?_⟩
  intro k hk hsmall z hz
  change 0 ≤ z 2 ∧ z 2 ≤ 2 ∧ |z 1| ≤ c0 * z 2 ∧
    |z 0| ≤ c0 * (2 - z 2) at hz
  have hx : |z 0| ≤ 2 * c0 := by nlinarith [c0_pos]
  have hy : |z 1| ≤ 2 * c0 := by nlinarith [c0_pos]
  rcases threshold_dichotomy hd k (z 0) (z 1) (z 2) with hfirst | hsecond
  · obtain ⟨p, hp, heq⟩ := hinc k (z 0) (z 1) (z 2) hk hsmall
      hx hz.1 hz.2.1 hz.2.2.1 hfirst
    left
    refine ⟨p, hp, z 0, hx, ?_⟩
    have h₀ := congrArg (fun q : Plane => q 0) heq
    have h₁ := congrArg (fun q : Plane => q 1) heq
    apply PiLp.ext
    intro i
    fin_cases i
    · rfl
    · exact h₀.symm
    · exact h₁.symm
  · obtain ⟨p, hp, heq⟩ := hinc k (-z 1) (z 0) (2 - z 2) hk hsmall
      (by simpa only [abs_neg] using hy) (by linarith [hz.2.1])
      (by linarith [hz.1]) hz.2.2.2 hsecond
    right
    refine ⟨p, hp, z 1, hy, ?_⟩
    have h₀ := congrArg (fun q : Plane => q 0) heq
    have h₁ := congrArg (fun q : Plane => q 1) heq
    apply PiLp.ext
    intro i
    fin_cases i
    · exact h₀.symm
    · rfl
    · change z 2 = 2 - lineMap d0 k (-z 1) p 1
      change lineMap d0 k (-z 1) p 1 = 2 - z 2 at h₁
      linarith

end RationalDictionary

end

end OAI

import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions
import OAI.Geometry.CylinderCovering.Rational.RationalThreshold

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace SlopeRational

theorem rational_cover_small {d : ℝ} (hd : 0 < d) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ ε q : ℝ,
      0 < ε → ε < δ → C * ε ^ 3 ≤ q →
      referenceTetrahedron ⊆ lowerSweep d ε q ∪ upperSweep d ε q := by
  obtain ⟨δ, C, hδ, hC, hinc⟩ := thresholdInclusion_main d hd
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro ε q he hsmall hq z hz
  obtain ⟨t, ht0, ht1, hx, hy, hz2⟩ := hz
  have hx1 : |z 0| ≤ 1 / 2 := by linarith
  have hy1 : |z 1| ≤ 1 / 2 := by linarith
  have ht : |t| ≤ 1 / 2 := abs_le.mpr ⟨ht0, ht1⟩
  have hwy : vec2 (z 1) t ∈ wedge := by
    change 2 * |z 1| ≤ 1 / 2 - t
    linarith
  have hwx : vec2 (z 0) (-t) ∈ wedge := by
    change 2 * |z 0| ≤ 1 / 2 - -t
    linarith
  rcases threshold_alternative hd ε (z 0) (z 1) t with hfirst | hsecond
  · obtain ⟨p, hp, hmap⟩ := hinc ε q (z 0) (z 1) t he hsmall hq hx1 hy1 ht hwy hfirst
    apply Or.inl
    refine ⟨p, hp, z 0, hx1, ?_⟩
    have hY := congrArg (fun w : Plane => w 0) hmap
    have hT := congrArg (fun w : Plane => w 1) hmap
    change p 0 + ε * z 0 * a d (p 0) (p 1) = z 1 at hY
    change p 1 + ε * z 0 * b d (p 0) (p 1) = t at hT
    ext i
    fin_cases i
    · rfl
    · change z 1 = p 0 + z 0 * (ε * a d (p 0) (p 1))
      nlinarith only [hY]
    · change z 2 = physicalScale * (p 1 + z 0 * (ε * b d (p 0) (p 1)))
      rw [hz2, ← hT]
      ring
  · obtain ⟨p, hp, hmap⟩ := hinc ε q (-(z 1)) (z 0) (-t) he hsmall hq
      (by simpa only [abs_neg] using hy1) hx1 (by simpa only [abs_neg] using ht) hwx hsecond
    apply Or.inr
    let w : Space := RuledApproximation.vec3 (z 1)
      (p 0 + z 1 * ((-ε • field d p) 0))
      (physicalScale * (p 1 + z 1 * ((-ε • field d p) 1)))
    refine ⟨w, ⟨p, hp, z 1, hy1, rfl⟩, ?_⟩
    have hY := congrArg (fun v : Plane => v 0) hmap
    have hT := congrArg (fun v : Plane => v 1) hmap
    change p 0 + ε * (-(z 1)) * a d (p 0) (p 1) = z 0 at hY
    change p 1 + ε * (-(z 1)) * b d (p 0) (p 1) = -t at hT
    ext i
    fin_cases i
    · change p 0 + z 1 * (-ε * a d (p 0) (p 1)) = z 0
      nlinarith only [hY]
    · rfl
    · change -(physicalScale * (p 1 + z 1 * (-ε * b d (p 0) (p 1)))) = z 2
      rw [hz2]
      have hid : p 1 + z 1 * (-ε * b d (p 0) (p 1)) = -t := by nlinarith only [hT]
      rw [hid]
      ring

theorem rationalCoverage_main : RationalCoverageStatement := by
  intro d q hd hqpos _hqO hqsmall
  obtain ⟨δ, C, hδ, hC, hcover⟩ := rational_cover_small hd
  have hepos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hesmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  have hbound := hqsmall.def (show 0 < 1 / C by positivity)
  filter_upwards [hepos, hesmall, hqpos, hbound] with ε he heδ hq hbound
  have hb : ε ^ 3 ≤ (1 / C) * q ε := by
    simpa only [Real.norm_eq_abs, abs_of_pos (pow_pos he 3), abs_of_pos hq] using hbound
  have hpad : C * ε ^ 3 ≤ q ε := by
    have hmul := mul_le_mul_of_nonneg_left hb hC.le
    have hne : C ≠ 0 := ne_of_gt hC
    field_simp [hne] at hmul
    nlinarith only [hmul]
  exact hcover ε (q ε) he heδ hpad

end SlopeRational

end

end OAI

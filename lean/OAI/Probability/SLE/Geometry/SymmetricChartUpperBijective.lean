import OAI.Probability.SLE.Geometry.RealSymmetricDiskMapSign

namespace OAI

/-! Restricting a symmetric disk chart to its upper component preserves
surjectivity onto the upper half disk. -/
noncomputable section
open Set Complex
open scoped ComplexConjugate

namespace SLEExactGauge

theorem symmetric_disk_chart_upper_bijOn {D : Set ℂ} {f : ℂ → ℂ}
    (hD : MapsTo conj D D) (hb : BijOn f D (Metric.ball 0 1))
    (hs : ∀ z ∈ D, f (conj z)=conj (f z))
    (hu : MapsTo f (D ∩ upperHalfPlane) upperHalfPlane) :
    BijOn f (D ∩ upperHalfPlane) (Metric.ball 0 1 ∩ upperHalfPlane) := by
  refine ⟨fun z hz => ⟨hb.mapsTo hz.1,hu hz⟩,hb.injOn.mono inter_subset_left,?_⟩
  intro w hw
  obtain ⟨z,hz,hzw⟩ := hb.surjOn hw.1
  refine ⟨z,⟨hz,?_⟩,hzw⟩
  by_contra hn
  have hzle : z.im ≤ 0 := le_of_not_gt hn
  by_cases hz0 : z.im=0
  · have hconj : conj z=z := by apply Complex.ext <;> simp [hz0]
    have he := hs z hz
    rw [hconj,hzw] at he
    have him := congrArg Complex.im he
    simp only [conj_im] at him
    have hwH := hw.2
    change 0 < w.im at hwH
    linarith
  · have hzneg : z.im < 0 := lt_of_le_of_ne hzle hz0
    have hcH : conj z ∈ upperHalfPlane := by
      change 0 < (conj z).im
      simpa only [conj_im] using neg_pos.mpr hzneg
    have hfH := hu ⟨hD hz,hcH⟩
    rw [hs z hz,hzw] at hfH
    change 0 < (conj w).im at hfH
    rw [conj_im] at hfH
    have hwH := hw.2
    change 0 < w.im at hwH
    linarith

end SLEExactGauge

end

end OAI

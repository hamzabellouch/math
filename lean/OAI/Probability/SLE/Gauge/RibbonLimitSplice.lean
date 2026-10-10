import OAI.Probability.SLE.Gauge.RibbonLimitPassageGeometry
import OAI.Probability.SLE.Geometry.GuideSplice

namespace OAI

/-! The limiting coordinate guide supplies the actual small-circle splice,
its open continuation region, and a target strictly beyond the next front. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge.RibbonCoordinates

def limitingFrontTarget (F : ℂ → ℂ) (p : ℂ → ℝ) (U : Set ℂ) : Set ℂ :=
  upperHalfPlane ∩ F ⁻¹' (U ∩ p ⁻¹' Ioi 1)

theorem limitingFrontTarget_isOpen
    (F : ℂ → ℂ) (hF : ContinuousOn F upperHalfPlane)
    (p : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U) (hp : ContinuousOn p U) :
    IsOpen (limitingFrontTarget F p U) :=
  hF.isOpen_inter_preimage isOpen_upperHalfPlane (hp.isOpen_inter_preimage hU isOpen_Ioi)

/-- No small-image or last-crossing hypothesis is needed for the limiting
splice: both follow from the actual continuous inverse guide and its
boundary value. -/
theorem limiting_guide_splice_geometry
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hi : InjOn F upperHalfPlane) (α β : ℝ → ℂ)
    (hα : ContinuousOn α (Icc 0 (3 / 2 : ℝ)))
    (hβ : ContinuousOn β (Icc 0 (3 / 2 : ℝ))) (hβ0 : β 0 = 0)
    (hβH : MapsTo β (Ioc 0 (3 / 2 : ℝ)) upperHalfPlane)
    (hrel : EqOn (F ∘ β) α (Ioc 0 (3 / 2 : ℝ)))
    (homit : α 0 ∉ F '' upperHalfPlane)
    (U : Set ℂ) (hU : IsOpen U) (p : ℂ → ℝ) (hp : ContinuousOn p U)
    (hαU : α '' Icc (0 : ℝ) (3 / 2) ⊆ U)
    (hprogress : ∀ t ∈ Icc (0 : ℝ) (3 / 2), p (α t) = t)
    (r m : ℝ) (hr : 0 < r) (hm : 0 < m) :
    ∃ B tB : ℝ, 0 < B ∧ B / 2 ≤ m ∧ 0 < tB ∧ tB < 3 / 2 ∧
      ‖β tB‖ = B ∧ (∀ t ∈ Ioc tB (3 / 2 : ℝ), B < ‖β t‖) ∧
      (∀ θ ∈ Ioo 0 Real.pi,
        ‖F (GuideSplice.circlePoint B θ) - α 0‖ < r / 4) ∧
      (∀ z : ℂ, B / 8 ≤ ‖z‖ → ‖z‖ ≤ B → ‖z‖ / 2 ≤ z.im →
        ‖F z - α 0‖ < r / 4) ∧
      F '' (β '' Icc tB (3 / 2 : ℝ)) ⊆ U ∧
      IsOpen (limitingFrontTarget F p U) ∧
      β (3 / 2) ∈ limitingFrontTarget F p U ∧
      (∀ z ∈ limitingFrontTarget F p U, 1 < p (F z)) := by
  have hT : (0 : ℝ) < 3 / 2 := by norm_num
  have ha0 := hα 0 ⟨le_rfl, hT.le⟩
  have haIoc : Tendsto α (𝓝[Ioc (0 : ℝ) (3 / 2)] 0) (𝓝 (α 0)) :=
    ha0.mono_left (nhdsWithin_mono _ Ioc_subset_Icc_self)
  have heq : (F ∘ β) =ᶠ[𝓝[Ioc (0 : ℝ) (3 / 2)] 0] α :=
    eventually_mem_nhdsWithin.mono (fun _ ht => hrel ht)
  have hlimit : Tendsto (F ∘ β) (𝓝[>] 0) (𝓝 (α 0)) := by
    rw [← nhdsWithin_Ioc_eq_nhdsGT hT]
    exact haIoc.congr' heq.symm
  have homit' : ∀ z, 0 < z.im → F z ≠ α 0 := by
    intro z hz he
    exact homit ⟨z, hz, he⟩
  have hendH : 0 < (β (3 / 2)).im := hβH ⟨hT, le_rfl⟩
  have hnorm : 0 < ‖β (3 / 2)‖ :=
    (lt_of_lt_of_le hendH (Complex.im_le_norm _))
  have hbound : 0 < min (2 * m) ‖β (3 / 2)‖ := lt_min (by positivity) hnorm
  obtain ⟨B, hB, hcircle, hsector⟩ :=
    SmallImageSemicircle.access_guide_has_arbitrarily_small_quarter_image_sector hF hi homit'
      hr hT hβ hβ0 (fun t ht => hβH ht) hlimit _ hbound
  have hBend : B < ‖β (3 / 2)‖ := hB.2.trans_le (min_le_right _ _)
  obtain ⟨tB, htB, hcross, hafter⟩ := GuideSplice.exists_last_circle_crossing hB.1 hT le_rfl
    hβ hβ0 (fun t ht => by have he : t = 3 / 2 := le_antisymm ht.2 ht.1; simpa only [he] using hBend)
  refine ⟨B, tB, hB.1, ?_, htB.1, htB.2, hcross, hafter, hcircle, hsector, ?_,
    limitingFrontTarget_isOpen F hF.continuousOn p U hU hp, ?_, ?_⟩
  · have hh := hB.2.trans_le (min_le_left _ _)
    linarith
  · rintro _ ⟨z, ⟨t, ht, rfl⟩, rfl⟩
    rw [show F (β t) = α t from hrel ⟨htB.1.trans_le ht.1, ht.2⟩]
    exact hαU (mem_image_of_mem α ⟨htB.1.le.trans ht.1, ht.2⟩)
  · refine ⟨hendH, ?_, ?_⟩
    · rw [show F (β (3 / 2)) = α (3 / 2) from hrel ⟨hT, le_rfl⟩]
      exact hαU (mem_image_of_mem α ⟨hT.le, le_rfl⟩)
    · change 1 < p (F (β (3 / 2)))
      rw [show F (β (3 / 2)) = α (3 / 2) from hrel ⟨hT, le_rfl⟩,
        hprogress _ ⟨hT.le, le_rfl⟩]
      norm_num
  · intro z hz
    exact hz.2.2

end SLEExactGauge.RibbonCoordinates

end

end OAI

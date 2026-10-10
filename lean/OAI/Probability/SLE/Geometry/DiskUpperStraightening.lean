import OAI.Probability.SLE.Geometry.DiskCrosscutBoundary

namespace OAI

/-! Straighten the disk crosscut with its exact parameter, while fixing
the upper semicircle. The second side is handled separately. -/
noncomputable section
open Set Complex

namespace SLEExactGauge

def diskDiameter (s : ℝ) : ℂ := ((2*s-1 : ℝ) : ℂ)

lemma diskDiameter_continuous : Continuous diskDiameter := by
  unfold diskDiameter
  fun_prop

lemma diskDiameter_injOn : InjOn diskDiameter (Icc 0 1) := by
  intro s _ t _ he
  have hh := Complex.ofReal_inj.mp he
  linarith

lemma diskDiameter_interior (s : ℝ) (hs : s ∈ Ioo 0 1) : ‖diskDiameter s‖ < 1 := by
  change ‖((2*s-1 : ℝ) : ℂ)‖ < 1
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact abs_lt.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩

theorem disk_crosscut_upper_straightening
    (p : ℝ → ℂ) (hc : ContinuousOn p (Icc 0 1)) (hi : InjOn p (Icc 0 1))
    (h0 : p 0=-1) (h1 : p 1=1) (hp : ∀ s ∈ Ioo 0 1, ‖p s‖ < 1) :
    ∃ H : ℂ ≃ₜ ℂ,
      (∀ s ∈ Icc 0 1, H (p s)=diskDiameter s) ∧
      ∀ z ∈ diskUpperArc '' Icc 0 1, H z=z := by
  classical
  let B : Set ℂ := diskUpperArc '' Icc 0 1
  have hB : IsClosed B := (isCompact_Icc.image diskUpperArc_continuous).isClosed
  have hq0 : diskDiameter 0=p 0 := by simp [diskDiameter,h0]
  have hq1 : diskDiameter 1=p 1 := by norm_num [diskDiameter,h1]
  let e := fixedArcBoundaryReplacement p diskDiameter B hc hi
    diskDiameter_continuous.continuousOn diskDiameter_injOn hB hq0 hq1
    (disk_crosscut_meets_upper_at_endpoints p hp)
    (disk_crosscut_meets_upper_at_endpoints diskDiameter diskDiameter_interior)
  obtain ⟨H,hH⟩ := complex_jordan_extension (disk_crosscut_upper_jordan p hc hi h0 h1 hp)
    (disk_crosscut_upper_jordan diskDiameter diskDiameter_continuous.continuousOn
      diskDiameter_injOn (by norm_num [diskDiameter]) (by norm_num [diskDiameter])
      diskDiameter_interior) e
  refine ⟨H,?_,?_⟩
  · intro s hs
    have hh := hH ⟨p s,Or.inl (mem_image_of_mem p hs)⟩
    apply hh.trans
    change (if hx : p s ∈ p '' Icc 0 1 then
      (arcParameterReplacement p diskDiameter hc hi diskDiameter_continuous.continuousOn
        diskDiameter_injOn ⟨p s,hx⟩ : ℂ) else p s)=diskDiameter s
    rw [dite_eq_left (mem_image_of_mem p hs)]
    exact arcParameterReplacement_apply p diskDiameter hc hi
      diskDiameter_continuous.continuousOn diskDiameter_injOn s hs
  · intro z hz
    have hh := hH ⟨z,Or.inr hz⟩
    apply hh.trans
    change (if hx : z ∈ p '' Icc 0 1 then
      (arcParameterReplacement p diskDiameter hc hi diskDiameter_continuous.continuousOn
        diskDiameter_injOn ⟨z,hx⟩ : ℂ) else z)=z
    split_ifs with hx
    · obtain ⟨s,hs,rfl⟩ := hx
      rw [arcParameterReplacement_apply p diskDiameter hc hi
        diskDiameter_continuous.continuousOn diskDiameter_injOn s hs]
      rcases disk_crosscut_meets_upper_at_endpoints p hp s hs hz with rfl | rfl
      · exact hq0
      · exact hq1
    · rfl

end SLEExactGauge

end

end OAI

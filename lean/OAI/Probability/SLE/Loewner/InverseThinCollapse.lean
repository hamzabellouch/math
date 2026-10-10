import OAI.Probability.SLE.Geometry.BoundarySeparationRectangle
import OAI.Probability.SLE.Loewner.InitialInverseTimeContinuity

namespace OAI

/-! Thin crossings whose physical images shrink to one point force
collapse of a whole real boundary interval in the limiting inverse. -/
noncomputable section
open Set Filter Function Complex Metric MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

theorem initialInverse_thin_crossing_collapse (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {R : ℝ} (hR : 0<R) (hp : ∀ t : unitInterval, ‖p t‖<R)
    {s : unitInterval} {t : ℕ → unitInterval} (ht : Tendsto t atTop (𝓝 s))
    {B : ℂ → ℂ} (hB : ContinuousOn B {z : ℂ | 0≤z.im})
    (hBF : ∀ z∈upperHalfPlane, B z=initialInverseChart p hi h0 hH s z)
    {a b : ℝ} {c : ℂ} {ε η : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hη : Tendsto η atTop (𝓝 0))
    (hlow : ∀ᶠ n in atTop, ∀ x∈Ioo a b, ∃ y∈Ioc 0 (η n),
      ‖initialInverseChart p hi h0 hH (t n) ((x:ℂ)+(y:ℂ)*I)-c‖≤ε n) :
    ∀ x∈Ioo a b, B (x:ℂ)=c := by
  intro x hx
  by_contra hne
  obtain ⟨a',b',H,δ,haa,hab,hbb,hHpos,hδ,hsep⟩ :=
    boundary_separation_rectangle hB hBF hx hne
  let L := max |a'| |b'|
  have hxL : ∀ u∈Ioo a' b', |u|≤L := by
    intro u hu
    exact abs_le.mpr ⟨by dsimp [L]; linarith [hu.1,neg_abs_le a',le_max_left |a'| |b'|],
      by dsimp [L]; linarith [hu.2,le_abs_self b',le_max_right |a'| |b'|]⟩
  let C := (volume (closedBall (0:ℂ) (L+2+3*R))).toReal
  have hC : 0≤C := ENNReal.toReal_nonneg
  let D := (b'-a')*δ^2
  have hD : 0<D := mul_pos (sub_pos.mpr hab) (sq_pos_of_pos hδ)
  let h := min H (min 1 (D/(2*(C+1))))
  have hh : 0<h := lt_min hHpos (lt_min zero_lt_one (div_pos hD (by positivity)))
  have hhH : h≤H := min_le_left _ _
  have hh1 : h≤1 := (min_le_right _ _).trans (min_le_left _ _)
  have hhD : h*(2*(C+1))≤D :=
    (le_div_iff₀ (by positivity : 0<2*(C+1))).mp
      ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : h*C<D := by nlinarith
  let K := (fun u : ℝ => (u:ℂ)+(h:ℂ)*I) '' Icc a' b'
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKH : K⊆upperHalfPlane := by
    rintro _ ⟨u,hu,rfl⟩
    simpa [upperHalfPlane] using hh
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_upperHalfPlane).mp
    (initialInverseChart_locallyUniform_continuous p hi h0 hH s) K hKH hK
  have hu' := ht.eventually ((Metric.tendstoUniformlyOn_iff.mp hu) δ hδ)
  have he' := hε.eventually (gt_mem_nhds hδ)
  have hη' := hη.eventually (gt_mem_nhds hh)
  obtain ⟨n,hn,he,hηn,hlown⟩ := (hu'.and (he'.and (hη'.and hlow))).exists
  have hhigh : ∀ u∈Ioo a' b', δ+ε n≤
      ‖initialInverseChart p hi h0 hH (t n) ((u:ℂ)+(h:ℂ)*I)-c‖ := by
    intro u huI
    have hdist := hn _ (mem_image_of_mem _ ⟨huI.1.le,huI.2.le⟩)
    have hs := hsep u ⟨huI.1.le,huI.2.le⟩ h ⟨hh,hhH⟩
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (initialInverseChart p hi h0 hH s ((u:ℂ)+(h:ℂ)*I))
      (initialInverseChart p hi h0 hH (t n) ((u:ℂ)+(h:ℂ)*I)) c
    rw [dist_eq_norm] at hdist
    linarith
  have hlow' : ∀ u∈Ioo a' b', ∃ y∈Ioc 0 h,
      ‖initialInverseChart p hi h0 hH (t n) ((u:ℂ)+(y:ℂ)*I)-c‖≤ε n := by
    intro u huI
    obtain ⟨y,hy,hyc⟩ := hlown u ⟨haa.trans huI.1,huI.2.trans hbb⟩
    exact ⟨y,⟨hy.1,hy.2.trans hηn.le⟩,hyc⟩
  have hbound := initialInverse_thin_crossing_bound p hi h0 hH hR hp (t n)
    hab hh hh1 hδ.le c hxL hhigh hlow'
  exact (not_le_of_gt hsmall) hbound

end SLEExactGauge

end

end OAI

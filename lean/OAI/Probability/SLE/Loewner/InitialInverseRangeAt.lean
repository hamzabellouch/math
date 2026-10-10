import OAI.Probability.SLE.Loewner.InitialInversePartialDomain

namespace OAI

/-! Exact image of an inverse-chart limit at an arbitrary initial time,
from either side of that time. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma initialInverse_limit_avoids_before_time (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) {s : unitInterval} (ht : Tendsto t atTop (𝓝 s))
    (u : unitInterval) (hu : u<s) : ∀ z∈upperHalfPlane, F z≠p u := by
  have hne : ∀ᶠ n in atTop, ∀ z∈upperHalfPlane,
      initialInverseChart p hi h0 hH (t n) z≠p u := by
    filter_upwards [ht.eventually (Ioi_mem_nhds hu)] with n hn
    exact fun _ hz => initialInverseChart_avoids_prefix p hi h0 hH (t n) u hn.le hz
  exact TauCeti.hurwitz_forall_ne isOpen_upperHalfPlane
    (convex_halfSpace_im_gt (0:ℝ)).isPreconnected
    (Eventually.of_forall fun n => initialInverseChart_differentiableOn p hi h0 hH (t n))
    hlim hne (initialInverse_limit_not_constant p hi h0 hH hlim (p u))

lemma initialInverse_limit_mapsTo_at (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) {s : unitInterval} (ht : Tendsto t atTop (𝓝 s)) :
    MapsTo F upperHalfPlane (upperHalfPlane \ range (initialSubarc p s)) := by
  have hopen : IsOpen (F '' upperHalfPlane) := by
    rcases (hF.analyticOnNhd isOpen_upperHalfPlane).is_constant_or_isOpen
      (convex_halfSpace_im_gt (0:ℝ)).isPreconnected with ⟨c,hc⟩ | ho
    · exact False.elim (initialInverse_limit_not_constant p hi h0 hH hlim c hc)
    · exact ho _ Subset.rfl isOpen_upperHalfPlane
  intro z hz
  have hpos : 0<(F z).im := lt_of_lt_of_le hz (initialInverse_limit_im_ge p hi h0 hH hlim hz)
  refine ⟨hpos,?_⟩
  rw [initialSubarc_range]
  rintro ⟨u,hu,heu⟩
  have hbefore := initialInverse_limit_avoids_before_time p hi h0 hH hlim ht
  by_cases hus : u<s
  · exact hbefore u hus z hz heu.symm
  have hus : u=s := le_antisymm hu.2 (le_of_not_gt hus)
  subst u
  by_cases hs : s=0
  · rw [hs,h0] at heu
    rw [← heu] at hpos
    exact (lt_irrefl (0:ℝ)) hpos
  have hp : p s∈F '' upperHalfPlane := ⟨z,hz,heu.symm⟩
  have hpre : p ⁻¹' (F '' upperHalfPlane)∈𝓝 s :=
    p.continuous.continuousAt.preimage_mem_nhds (hopen.mem_nhds hp)
  have hcl : s∈closure (Iio s) := by
    rw [closure_Iio' (show (Iio s).Nonempty from ⟨0,bot_lt_iff_ne_bot.mpr hs⟩)]
    exact mem_Iic.mpr le_rfl
  obtain ⟨v,hvp,hvs⟩ := mem_closure_iff_nhds.mp hcl _ hpre
  obtain ⟨w,hw,hew⟩ := hvp
  exact hbefore v hvs w hw hew

theorem initialInverse_limit_bijOn_at (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) {s : unitInterval} (ht : Tendsto t atTop (𝓝 s)) :
    BijOn F upperHalfPlane (upperHalfPlane \ range (initialSubarc p s)) :=
  ⟨initialInverse_limit_mapsTo_at p hi h0 hH hF hlim ht,
    initialInverse_limit_injOn p hi h0 hH hlim,
    initialInverse_limit_covers_at p hi h0 hH hF hlim ht⟩

end SLEExactGauge

end

end OAI

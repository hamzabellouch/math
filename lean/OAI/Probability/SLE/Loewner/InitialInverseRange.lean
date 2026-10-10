import OAI.Probability.SLE.Loewner.InitialInverseCommonDomain
import Mathlib.Topology.Order.DenselyOrdered

namespace OAI

/-! At the terminal initial-arc time, the inverse limits have exactly the
prescribed slit domain as their image. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma initialInverseChart_avoids_prefix (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (t u : unitInterval) (hut : u≤t) {z : ℂ} (hz : z∈upperHalfPlane) :
    initialInverseChart p hi h0 hH t z≠p u := by
  by_cases ht : t=0
  · have hu : u=0 := le_antisymm (ht ▸ hut) bot_le
    simp only [ht,initialInverseChart_zero,id_eq,hu,h0]
    intro he
    have hh : 0<z.im := hz
    simp [he] at hh
  · rw [initialInverseChart,dite_eq_right ht]
    intro he
    have hm := (initialSlitChart p hi h0 hH t ht).inverse_mapsTo hz
    apply hm.2
    rw [he,initialSubarc_range]
    exact mem_image_of_mem p ⟨bot_le,hut⟩

lemma initialInverse_limit_not_constant (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) (c : ℂ) : ¬ ∀ z∈upperHalfPlane, F z=c := by
  intro hc
  have hinj := initialInverse_limit_injOn p hi h0 hH hlim
  have h1 : I∈upperHalfPlane := by simp [upperHalfPlane]
  have h2 : 2*I∈upperHalfPlane := by simp [upperHalfPlane]
  have he := hinj h1 h2 ((hc I h1).trans (hc (2*I) h2).symm)
  have hh := congrArg Complex.im he
  norm_num at hh

lemma initialInverse_limit_avoids_before_one (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) (ht : Tendsto t atTop (𝓝 1))
    (u : unitInterval) (hu : u<1) : ∀ z∈upperHalfPlane, F z≠p u := by
  have hne : ∀ᶠ n in atTop, ∀ z∈upperHalfPlane,
      initialInverseChart p hi h0 hH (t n) z≠p u := by
    filter_upwards [ht.eventually (Ioi_mem_nhds hu)] with n hn
    exact fun _ hz => initialInverseChart_avoids_prefix p hi h0 hH (t n) u hn.le hz
  exact TauCeti.hurwitz_forall_ne isOpen_upperHalfPlane
    (convex_halfSpace_im_gt (0:ℝ)).isPreconnected
    (Eventually.of_forall fun n => initialInverseChart_differentiableOn p hi h0 hH (t n))
    hlim hne (initialInverse_limit_not_constant p hi h0 hH hlim (p u))

lemma initialInverse_limit_mapsTo_final (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) (ht : Tendsto t atTop (𝓝 1)) :
    MapsTo F upperHalfPlane (upperHalfPlane \ range p) := by
  have hopen : IsOpen (F '' upperHalfPlane) := by
    rcases (hF.analyticOnNhd isOpen_upperHalfPlane).is_constant_or_isOpen
      (convex_halfSpace_im_gt (0:ℝ)).isPreconnected with ⟨c,hc⟩ | ho
    · exact False.elim (initialInverse_limit_not_constant p hi h0 hH hlim c hc)
    · exact ho _ Subset.rfl isOpen_upperHalfPlane
  intro z hz
  refine ⟨lt_of_lt_of_le hz (initialInverse_limit_im_ge p hi h0 hH hlim hz),?_⟩
  rintro ⟨u,hu⟩
  have hbefore := initialInverse_limit_avoids_before_one p hi h0 hH hlim ht
  by_cases hu1 : u<1
  · exact hbefore u hu1 z hz hu.symm
  have heu : u=1 := le_antisymm le_top (le_of_not_gt hu1)
  subst u
  have hp1 : p 1∈F '' upperHalfPlane := ⟨z,hz,hu.symm⟩
  have hpre : p ⁻¹' (F '' upperHalfPlane)∈𝓝 (1:unitInterval) :=
    p.continuous.continuousAt.preimage_mem_nhds (hopen.mem_nhds hp1)
  have hcl : (1:unitInterval)∈closure (Iio (1:unitInterval)) := by
    rw [closure_Iio' (show (Iio (1:unitInterval)).Nonempty from ⟨0,by norm_num⟩)]
    exact mem_Iic.mpr (le_refl (1:unitInterval))
  obtain ⟨v,hvp,hvlt⟩ := mem_closure_iff_nhds.mp hcl _ hpre
  obtain ⟨w,hw,hew⟩ := hvp
  exact hbefore v hvlt w hw hew

theorem initialInverse_limit_bijOn_final (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) (ht : Tendsto t atTop (𝓝 1)) :
    BijOn F upperHalfPlane (upperHalfPlane \ range p) :=
  ⟨initialInverse_limit_mapsTo_final p hi h0 hH hF hlim ht,
    initialInverse_limit_injOn p hi h0 hH hlim,
    initialInverse_limit_covers_final_domain p hi h0 hH hF hlim⟩

end SLEExactGauge

end

end OAI

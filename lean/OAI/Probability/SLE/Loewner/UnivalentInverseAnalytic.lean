import Mathlib

namespace OAI

/-! The local inverse of an injective holomorphic map is holomorphic.
The proof uses the open mapping theorem and removes the isolated possible
singularity of the inverse, without a conformal mapping assumption. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

lemma univalent_not_eventually_constant {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hi : InjOn f D) {a : ℂ} (ha : a ∈ D) :
    ¬∀ᶠ z in 𝓝 a, f z=f a := by
  intro h
  have he : ∀ᶠ z in 𝓝[≠] a, z=a := by
    filter_upwards [h.filter_mono nhdsWithin_le_nhds,
      (show ∀ᶠ z in 𝓝 a, z∈D from hD.mem_nhds ha).filter_mono
        nhdsWithin_le_nhds] with z hz hDz
    exact hi hDz ha hz
  have hn : ∀ᶠ z in 𝓝[≠] a, z≠a := self_mem_nhdsWithin
  obtain ⟨z,hz,hnz⟩ := (he.and hn).exists
  exact hnz hz

lemma univalent_nhds_le_map {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) (hi : InjOn f D)
    {a : ℂ} (ha : a ∈ D) : 𝓝 (f a) ≤ map f (𝓝 a) :=
  ((hf.analyticAt (hD.mem_nhds ha)).eventually_constant_or_nhds_le_map_nhds).resolve_left
    (univalent_not_eventually_constant hD hi ha)

lemma univalent_inverse_continuousAt {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) (hi : InjOn f D)
    {a : ℂ} (ha : a ∈ D) : ContinuousAt (invFunOn f D) (f a) := by
  have hleft : (invFunOn f D ∘ f) =ᶠ[𝓝 a] id := by
    filter_upwards [hD.mem_nhds ha] with z hz
    exact hi.leftInvOn_invFunOn hz
  change map (invFunOn f D) (𝓝 (f a)) ≤ 𝓝 (invFunOn f D (f a))
  rw [hi.leftInvOn_invFunOn ha]
  calc
    map (invFunOn f D) (𝓝 (f a)) ≤ map (invFunOn f D) (map f (𝓝 a)) :=
      Filter.map_mono (univalent_nhds_le_map hD hf hi ha)
    _ = 𝓝 a := by rw [Filter.map_map,Filter.map_congr hleft,Filter.map_id]

lemma univalent_deriv_eventually_ne {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) (hi : InjOn f D)
    {a : ℂ} (ha : a ∈ D) : ∀ᶠ z in 𝓝[≠] a, deriv f z≠0 := by
  have han := hf.analyticAt (hD.mem_nhds ha)
  apply (han.deriv.eventually_eq_or_eventually_ne analyticAt_const).resolve_left
  intro hz
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_ball.mem_iff.mp (hz.and (hD.mem_nhds ha))
  have hbD : ball a r ⊆ D := fun z hz => (hball hz).2
  have he : ∀ᶠ z in 𝓝 a, f z=f a := by
    filter_upwards [ball_mem_nhds a hr] with z hz
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball a r).isPreconnected
      (hf.mono hbD) (fun w hw => (hball hw).1) hz (mem_ball_self hr)
  exact univalent_not_eventually_constant hD hi ha he

lemma univalent_inverse_analyticAt {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) (hi : InjOn f D)
    {a : ℂ} (ha : a ∈ D) : AnalyticAt ℂ (invFunOn f D) (f a) := by
  have hc := univalent_inverse_continuousAt hD hf hi ha
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
  have hne : ∀ᶠ z in 𝓝 a, z≠a → deriv f z≠0 :=
    eventually_nhdsWithin_iff.mp (univalent_deriv_eventually_ne hD hf hi ha)
  have hpre : ∀ᶠ w in 𝓝 (f a), invFunOn f D w ≠ a → deriv f (invFunOn f D w) ≠ 0 := by
    have hg : Tendsto (invFunOn f D) (𝓝 (f a)) (𝓝 a) := by
      simpa only [hi.leftInvOn_invFunOn ha] using hc.tendsto
    exact hg.eventually hne
  have himage : f '' D ∈ 𝓝 (f a) :=
    univalent_nhds_le_map hD hf hi ha (image_mem_map (hD.mem_nhds ha))
  filter_upwards [hpre.filter_mono nhdsWithin_le_nhds,
    (show ∀ᶠ w in 𝓝 (f a), w ∈ f '' D from himage).filter_mono nhdsWithin_le_nhds,
    (show ∀ᶠ w in 𝓝[≠] (f a), w≠f a from self_mem_nhdsWithin)] with w hn hw hwa
  have hzD := (surjOn_image f D).mapsTo_invFunOn hw
  have hright := (surjOn_image f D).rightInvOn_invFunOn hw
  have hz : invFunOn f D w≠a := by
    intro h
    exact hwa (hright.symm.trans (congrArg f h))
  have hleft : ∀ᶠ z in 𝓝 (invFunOn f D w), invFunOn f D (f z)=z := by
    filter_upwards [hD.mem_nhds hzD] with z hz
    exact hi.leftInvOn_invFunOn hz
  have hd := (hf.analyticAt (hD.mem_nhds hzD)).hasStrictDerivAt.to_local_left_inverse
    (g := invFunOn f D) (hn hz) hleft
  rw [hright] at hd
  exact hd.hasDerivAt.differentiableAt

lemma univalent_deriv_ne_zero {D : Set ℂ} {f : ℂ → ℂ}
    (hD : IsOpen D) (hf : DifferentiableOn ℂ f D) (hi : InjOn f D)
    {a : ℂ} (ha : a ∈ D) : deriv f a≠0 := by
  have hg := (univalent_inverse_analyticAt hD hf hi ha).differentiableAt.hasDerivAt
  have h := hg.comp a (hf.differentiableAt (hD.mem_nhds ha)).hasDerivAt
  have he : (invFunOn f D ∘ f) =ᶠ[𝓝 a] id := by
    filter_upwards [hD.mem_nhds ha] with z hz
    exact hi.leftInvOn_invFunOn hz
  have hid := (he.hasDerivAt_iff).mp h
  have hone := hid.unique (hasDerivAt_id a)
  intro hz
  exact zero_ne_one (by simpa only [hz,mul_zero] using hone)

end SLEExactGauge

end

end OAI

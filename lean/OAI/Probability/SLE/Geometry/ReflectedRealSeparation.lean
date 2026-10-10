import OAI.Probability.SLE.Loewner.ReflectedForwardContinuity
import OAI.Probability.SLE.Loewner.SlitBoundaryTip

namespace OAI

/-! A real point different from the root never maps to the driving tip
under the normalized analytic continuation of an initial slit chart. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

theorem initialReflectedForward_ne_driver (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {s : unitInterval} (hs : s<1) {x : ℝ} (hx : x≠0) :
    initialReflectedForward p hi h0 hH s (x:ℂ)≠(initialDrivingValue p hi h0 hH s hs:ℂ) := by
  let G := initialReflectedForward p hi h0 hH s
  have hD : IsOpen (reflectedArcSet p)ᶜ :=
    ((isCompact_range p.continuous).union
      ((isCompact_range p.continuous).image Complex.continuous_conj)).isClosed.isOpen_compl
  have hxD : (x:ℂ)∈(reflectedArcSet p)ᶜ := real_not_reflected_arc p h0 hH hx
  have hc : ContinuousAt G (x:ℂ) :=
    ((initialReflectedForward_differentiable p hi h0 hH s).differentiableAt
      (hD.mem_nhds hxD)).continuousAt
  let v := fun y : ℝ => (x:ℂ)+(y:ℂ)*I
  have hv : Tendsto v (𝓝[>] (0:ℝ)) (𝓝 (x:ℂ)) := by
    have h : Continuous v := by dsimp [v]; fun_prop
    simpa only [v,ofReal_zero,zero_mul,add_zero] using
      (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have hm : ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ), v y∈upperHalfPlane ∩ (reflectedArcSet p)ᶜ := by
    filter_upwards [self_mem_nhdsWithin,hv.eventually (hD.mem_nhds hxD)] with y hy hyD
    exact ⟨by simpa [v,upperHalfPlane] using hy,hyD⟩
  obtain ⟨B,hBc,hBF,hBu⟩ := exists_initial_inverse_boundary_tip p hi h0 hH hs
  have hGmem : ∀ᶠ y : ℝ in 𝓝[>] (0:ℝ), G (v y)∈{z : ℂ | 0 ≤ z.im} := by
    filter_upwards [hm] with y hy
    have hd : v y∈upperHalfPlane \ range (initialSubarc p s) :=
      ⟨hy.1,fun he => hy.2 (reflected_initial_subset p s (Or.inl he))⟩
    rw [show G (v y)=initialForwardChart p hi h0 hH s (v y) from
      initialReflectedForward_eq p hi h0 hH s hd]
    exact (show 0<(initialForwardChart p hi h0 hH s (v y)).im from
      initialForwardChart_mem_upper p hi h0 hH s hd).le
  have hq : G (x:ℂ)∈{z : ℂ | 0 ≤ z.im} := by
    change 0 ≤ (initialReflectedForward p hi h0 hH s (x:ℂ)).im
    rw [initialReflectedForward_real p hi h0 hH s hx]
  have hlim := (hBc _ hq).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hc.tendsto.comp hv,hGmem⟩)
  have hleft : B (G (x:ℂ))=(x:ℂ) := by
    apply tendsto_nhds_unique hlim
    apply hv.congr'
    filter_upwards [hm] with y hy
    have hd : v y∈upperHalfPlane \ range (initialSubarc p s) :=
      ⟨hy.1,fun he => hy.2 (reflected_initial_subset p s (Or.inl he))⟩
    have he : G (v y)=initialForwardChart p hi h0 hH s (v y) :=
      initialReflectedForward_eq p hi h0 hH s hd
    symm
    change B (G (v y))=v y
    rw [he,hBF _ (initialForwardChart_mem_upper p hi h0 hH s hd),
      initialInverse_forward_at p hi h0 hH s hd]
  intro he
  change G (x:ℂ)=(initialDrivingValue p hi h0 hH s hs:ℂ) at he
  rw [he,hBu] at hleft
  by_cases hs0 : s=0
  · rw [hs0,h0] at hleft
    exact hx (ofReal_eq_zero.mp hleft.symm)
  · have hp := hH s hs0
    rw [hleft] at hp
    simp [upperHalfPlane] at hp

end SLEExactGauge

end

end OAI

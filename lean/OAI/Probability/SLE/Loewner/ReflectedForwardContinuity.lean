import OAI.Probability.SLE.Loewner.InitialReflectedForward
import OAI.Probability.SLE.Geometry.HalfPlaneBoundaryExtension
import TauCeti.Analysis.Complex.Conformal.NormalFamilies

namespace OAI

/-! Uniform analytic bounds carry time continuity of the initial slit
maps from the open half-plane to the surviving real boundary. -/
noncomputable section
open Set Filter Function Complex Metric
open scoped Topology

namespace SLEExactGauge

lemma initialReflectedForward_equicontinuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane) :
    EquicontinuousOn (initialReflectedForward p hi h0 hH) (reflectedArcSet p)ᶜ := by
  have hb : TauCeti.IsLocallyBoundedOn (initialReflectedForward p hi h0 hH)
      (reflectedArcSet p)ᶜ := by
    intro K hKD hK
    obtain ⟨A,hA⟩ := hK.isBounded.exists_norm_le
    obtain ⟨B,hB⟩ := (isCompact_range p.continuous).isBounded.exists_norm_le
    let R := |A|+|B|+1
    have hR : 0<R := by dsimp [R]; positivity
    have hp (s : unitInterval) : ‖p s‖<R := by
      have hh := hB _ (mem_range_self s)
      dsimp [R]
      linarith [le_abs_self B,abs_nonneg A]
    refine ⟨(512*Real.pi+9)*R,?_⟩
    intro s z hz
    apply initialReflectedForward_uniform_bound p hi h0 hH hR hp s (hKD hz)
    have hh := hA z hz
    dsimp [R]
    linarith [le_abs_self A,abs_nonneg B]
  exact hb.equicontinuousOn
    ((isCompact_range p.continuous).union
      ((isCompact_range p.continuous).image Complex.continuous_conj)).isClosed.isOpen_compl
    (initialReflectedForward_differentiable p hi h0 hH)

lemma initialReflectedForward_equicontinuousAt_real (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {x : ℝ} (hx : x≠0) :
    EquicontinuousAt (initialReflectedForward p hi h0 hH) (x:ℂ) := by
  have hD : IsOpen (reflectedArcSet p)ᶜ :=
    ((isCompact_range p.continuous).union
      ((isCompact_range p.continuous).image Complex.continuous_conj)).isClosed.isOpen_compl
  have hxD : (x:ℂ)∈(reflectedArcSet p)ᶜ := real_not_reflected_arc p h0 hH hx
  have hh := initialReflectedForward_equicontinuous p hi h0 hH (x:ℂ) hxD
  simpa only [EquicontinuousWithinAt,EquicontinuousAt,nhdsWithin_eq_nhds.mpr (hD.mem_nhds hxD)] using hh

theorem initialReflectedForward_real_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
    {x : ℝ} (hx : x≠0) :
    Continuous (fun s => initialReflectedForward p hi h0 hH s (x:ℂ)) := by
  have hD : IsOpen (reflectedArcSet p)ᶜ :=
    ((isCompact_range p.continuous).union
      ((isCompact_range p.continuous).image Complex.continuous_conj)).isClosed.isOpen_compl
  have hxD : (x:ℂ)∈(reflectedArcSet p)ᶜ := real_not_reflected_arc p h0 hH hx
  apply continuous_iff_continuousAt.mpr
  intro s
  apply (initialReflectedForward_equicontinuousAt_real p hi h0 hH hx).tendsto_of_mem_closure
    (((initialReflectedForward_differentiable p hi h0 hH s).differentiableAt
      (hD.mem_nhds hxD)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (s := upperHalfPlane ∩ (reflectedArcSet p)ᶜ)
  · intro z hz
    have hzD (t : unitInterval) : z∈upperHalfPlane \ range (initialSubarc p t) :=
      ⟨hz.1,fun he => hz.2 (reflected_initial_subset p t (Or.inl he))⟩
    have hc : Continuous (fun t => initialForwardChart p hi h0 hH t z) := by
      apply SeqContinuous.continuous
      intro t r ht
      exact initialForwardChart_tendsto p hi h0 hH ht tendsto_const_nhds (hzD r) (fun n => hzD (t n))
    have he : (fun t => initialReflectedForward p hi h0 hH t z)=
        (fun t => initialForwardChart p hi h0 hH t z) :=
      funext (fun t => initialReflectedForward_eq p hi h0 hH t (hzD t))
    simpa only [he,initialReflectedForward_eq p hi h0 hH s (hzD s)] using hc.continuousAt.tendsto
  · exact hD.closure_inter ⟨closedHalfPlane_subset_closure_upperHalfPlane (by simp),hxD⟩

end SLEExactGauge

end

end OAI

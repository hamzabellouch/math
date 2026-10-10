import OAI.Probability.SLE.Loewner.FutureSlitDomain
import OAI.Probability.SLE.Loewner.InitialChartNormalization

namespace OAI

/-! Forward and inverse charts obtained by removing a future segment
after an initial slit. The real translation keeps their normalization. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

variable (p : C(unitInterval,ℂ)) (hi : Injective p) (h0 : p 0=0)
  (hH : ∀ t : unitInterval, t≠0 → p t∈upperHalfPlane)
  {s t : unitInterval} (hst : s<t) (ht : t<1)

noncomputable def futureComposedForward (z : ℂ) : ℂ :=
  (initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ)+
    (futureSlitChart p hi h0 hH hst ht).forward
      (initialForwardChart p hi h0 hH s z-
        (initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ))

noncomputable def futureComposedInverse (z : ℂ) : ℂ :=
  initialInverseChart p hi h0 hH s
    ((initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ)+
      (futureSlitChart p hi h0 hH hst ht).inverse
        (z-(initialDrivingValue p hi h0 hH s (hst.trans ht):ℂ)))

theorem future_composed_chart_properties :
    DifferentiableOn ℂ (futureComposedForward p hi h0 hH hst ht)
      (upperHalfPlane \ range (initialSubarc p t)) ∧
    DifferentiableOn ℂ (futureComposedInverse p hi h0 hH hst ht) upperHalfPlane ∧
    MapsTo (futureComposedForward p hi h0 hH hst ht)
      (upperHalfPlane \ range (initialSubarc p t)) upperHalfPlane ∧
    MapsTo (futureComposedInverse p hi h0 hH hst ht)
      upperHalfPlane (upperHalfPlane \ range (initialSubarc p t)) ∧
    (∀ z∈upperHalfPlane \ range (initialSubarc p t),
      futureComposedInverse p hi h0 hH hst ht (futureComposedForward p hi h0 hH hst ht z)=z) ∧
    ∀ z∈upperHalfPlane,
      futureComposedForward p hi h0 hH hst ht (futureComposedInverse p hi h0 hH hst ht z)=z := by
  let U : ℝ := initialDrivingValue p hi h0 hH s (hst.trans ht)
  let Q := futureSlitChart p hi h0 hH hst ht
  have hshift : MapsTo (fun z : ℂ => z-(U:ℂ)) upperHalfPlane upperHalfPlane := by
    intro z hz
    change 0<(z-(U:ℂ)).im
    simpa only [sub_im,ofReal_im,sub_zero] using (show 0<z.im from hz)
  have hadd : MapsTo (fun z : ℂ => (U:ℂ)+z) upperHalfPlane upperHalfPlane := by
    intro z hz
    change 0<((U:ℂ)+z).im
    simpa only [add_im,ofReal_im,zero_add] using (show 0<z.im from hz)
  have hsub : upperHalfPlane \ range (initialSubarc p t) ⊆
      upperHalfPlane \ range (initialSubarc p s) := by
    intro z hz
    exact ⟨hz.1,fun he => hz.2 (initialSubarc_range_mono p hst.le he)⟩
  have hA := initialForward_centered_bijOn p hi h0 hH hst ht
  have hJH : MapsTo Q.inverse upperHalfPlane upperHalfPlane :=
    fun _ hz => (Q.inverse_mapsTo hz).1
  have hinner : MapsTo (fun z : ℂ => (U:ℂ)+Q.inverse (z-(U:ℂ)))
      upperHalfPlane upperHalfPlane := hadd.comp (hJH.comp hshift)
  have hFin : MapsTo (futureComposedInverse p hi h0 hH hst ht)
      upperHalfPlane (upperHalfPlane \ range (initialSubarc p t)) := by
    intro z hz
    have hb := initialInverseChart_mem_domain p hi h0 hH s (hinner hz)
    apply (initialForward_centered_mem_domain_iff p hi h0 hH hst ht hb).mp
    change initialForwardChart p hi h0 hH s
      (initialInverseChart p hi h0 hH s ((U:ℂ)+Q.inverse (z-(U:ℂ))))-(U:ℂ)∈
        upperHalfPlane \ range (centeredFutureArc p hi h0 hH hst ht)
    rw [initialForward_inverse p hi h0 hH s (hinner hz),add_sub_cancel_left]
    exact Q.inverse_mapsTo (hshift hz)
  refine ⟨?_,?_,?_,hFin,?_,?_⟩
  · apply DifferentiableOn.const_add
    exact Q.forward_differentiable.comp
      (((initialForwardChart_differentiableOn_current p hi h0 hH s).mono hsub).sub_const _) hA.mapsTo
  · exact (initialInverseChart_differentiableOn p hi h0 hH s).comp
      ((Q.inverse_differentiable.comp (differentiableOn_id.sub_const _) hshift).const_add _) hinner
  · intro z hz
    exact hadd (Q.bijOn.mapsTo (hA.mapsTo hz))
  · intro z hz
    change initialInverseChart p hi h0 hH s ((U:ℂ)+Q.inverse
      (((U:ℂ)+Q.forward (initialForwardChart p hi h0 hH s z-(U:ℂ)))-(U:ℂ)))=z
    rw [add_sub_cancel_left,Q.left_inverse _ (hA.mapsTo hz),add_sub_cancel,
      initialInverse_forward_at p hi h0 hH s (hsub hz)]
  · intro z hz
    change (U:ℂ)+Q.forward (initialForwardChart p hi h0 hH s
      (initialInverseChart p hi h0 hH s ((U:ℂ)+Q.inverse (z-(U:ℂ))))-(U:ℂ))=z
    rw [initialForward_inverse p hi h0 hH s (hinner hz),add_sub_cancel_left,
      Q.right_inverse _ (hshift hz),add_sub_cancel]

end SLEExactGauge

end

end OAI

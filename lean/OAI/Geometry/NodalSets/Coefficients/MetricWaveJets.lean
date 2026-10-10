import OAI.Geometry.NodalSets.Charts.GeometricContact
import OAI.Geometry.NodalSets.Coefficients.GlobalWaveResidual
import OAI.Geometry.NodalSets.Elliptic.CompactNormalOperator
import OAI.Geometry.NodalSets.Waves.NormalFrameWaveJet

namespace OAI

namespace Yau.Geometry
open Filter Set MvPolynomial
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

structure MetricWaveJetFamily
    (G : T → Fin 4 → Fin 4 → Coord → ℂ) (b : T → Fin 4 → Coord → ℂ)
    (s a bb : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ) (m J : ℕ)
    (phi : T → CPoly) (A : ℕ → T → CPoly) : Prop where
  phase_continuous : ContinuousPolyFamily phi
  amplitude_continuous : ∀ j, ContinuousPolyFamily (A j)
  phase_retained : ∀ t k, k ≤ 2 → homogeneousComponent k (phi t) =
    initialPhaseJet (s t) (normalFrameVector (a t) (bb t)) (normalComplexHessian (a t) (bb t) (H t)) k
  phase_degree : ∀ t d, m+2*J+3 < d → homogeneousComponent d (phi t) = 0
  amplitude_value : ∀ j t, homogeneousComponent 0 (A j t) = if j=0 then 1 else 0
  amplitude_degree : ∀ j t k, m+1+2*(J-j) < k → homogeneousComponent k (A j t) = 0
  eikonal_flat : ∀ t, FlatAt m (smoothEikonal (G t) (reval (phi t))) 0
  transport_zero : ∀ t, FlatAt m (smoothTransport (smoothBeamVector (G t) (reval (phi t)))
    (smoothBeamScalar (G t) (b t) (reval (phi t))) (fun _ ↦ 0) (reval (A 0 t))) 0
  transport_next : ∀ j, j < J → ∀ t, FlatAt m
    (smoothTransport (smoothBeamVector (G t) (reval (phi t)))
      (smoothBeamScalar (G t) (b t) (reval (phi t)))
      (fun x ↦ -smoothSecondOrder (G t) (b t) (reval (A j t)) x) (reval (A (j+1) t))) 0

omit [CompactSpace T] in
theorem NormalOperatorFamily.solve_jets
    {G : T → Fin 4 → Fin 4 → Coord → ℂ} {b : T → Fin 4 → Coord → ℂ}
    (hG : NormalOperatorFamily G b) (a bb s : T → ℝ) (H : T → Fin 4 → Fin 4 → ℝ)
    (ha : Continuous a) (hbb : Continuous bb) (hs : Continuous s)
    (hHc : ∀ i j, Continuous (fun t ↦ H t i j))
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0)
    (hlen : ∀ t, bb t^2 = a t^2+4) (hH : ∀ t i j, H t i j = H t j i)
    (m J : ℕ) (hm : 1 ≤ m) :
    ∃ phi A, MetricWaveJetFamily G b s a bb H m J phi A := by
  obtain ⟨hAc,hBc,hA0,hA1,hAj,hBj⟩ := hG.matching_taylor m hm
  obtain ⟨phi,A,hp,hA,hkeep,hdeg,hv,had,hE,hT,hTj⟩ := normal_frame_smooth_wave_jets_continuous
    a bb s H ha hbb hs hHc ha0 hb0 hlen hH G b
    (fun t i j ↦ taylorPolynomial (G t i j) 0 m)
    (fun t j ↦ taylorPolynomial (b t j) 0 m) hAc hBc hG.principal_smooth hG.drift_smooth
    hA0 hA1 m J hAj hBj
  exact ⟨phi,A,⟨hp,hA,hkeep,hdeg,hv,had,hE,hT,hTj⟩⟩

theorem compact_actual_metric_wave_jets
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → Coord) (hy : Continuous y) (e : T → Coord ≃L[ℝ] Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    {U : Set Coord} (hU : IsOpen U) (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
    (q : T → Coord) (a bb : T → ℝ) (ha : Continuous a) (hbb : Continuous bb)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0) (hlen : ∀ t, bb t^2 = a t^2+4)
    (hap : ∀ t, a t • e t (Pi.single 0 1) = metricGradient g S (y t))
    (hbq : ∀ t, bb t • e t (Pi.single 1 1) = q t)
    (hstrict : ∀ t, 0 < sourceHessian g S (y t) (metricGradient g S (y t)) (metricGradient g S (y t)) +
      sourceHessian g S (y t) (q t) (q t)) (m J : ℕ) (hm : 1 ≤ m) :
    ∃ (beta : ContDiffBump (0:Coord)) (phi : T → CPoly) (A : ℕ → T → CPoly),
      NormalOperatorFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta) ∧
      MetricWaveJetFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta)
        (fun t ↦ S (y t)) a bb
        (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) m J phi A ∧
      ∃ c > 0, ∀ᶠ N : ℝ in atTop, ∀ t, ∀ x : Coord, ‖x‖ ≤ 2*N^(-1/3:ℝ) →
        (reval (phi t) x).re-S (actualMetricChart g (y t) (e t) x) ≤ -c*‖x‖^2 := by
  obtain ⟨beta,_,hG⟩ := compact_actual_normal_operator g hg hs hpos w hw y hy e he ho hU hyU hwpos
  have hconn := actualFrameConnection_continuous g hg hpos y hy e he
  have hSc (k : ℕ) : Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k
      (S ∘ actualMetricChart g (y z.1) (e z.1)) z.2) :=
    charted_scalar_spatial_jets S hS y hy e he _ hconn k
  obtain ⟨phi,A,hjets⟩ := hG.solve_jets a bb (fun t ↦ S (y t))
    (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) ha hbb
    (hS.continuous.comp hy) (envelopeHessian_family_continuous _ (hSc 2)) ha0 hb0 hlen
    (fun t ↦ envelopeHessian_symmetric _ (hS.comp (quadraticChartMap_smooth _ _ _))) m J hm
  obtain ⟨c,hc,hgap⟩ := actual_metric_chart_phase_contact isCompact_univ g hg hs hpos S hS y hy e he ho
    q a bb ha hbb ha0 hb0 hap hbq (fun t _ ↦ hstrict t) phi hjets.phase_continuous
    (fun t _ ↦ hjets.phase_retained t)
  exact ⟨beta,phi,A,hG,hjets,c,hc,hgap.mono (fun _ h t ↦ h t (mem_univ t))⟩

theorem MetricWaveJetFamily.global_residual
    {G : T → Fin 4 → Fin 4 → Coord → ℂ} {b : T → Fin 4 → Coord → ℂ}
    (hG : NormalOperatorFamily G b) {s a bb : T → ℝ} {H : T → Fin 4 → Fin 4 → ℝ}
    {m J : ℕ} {phi : T → CPoly} {A : ℕ → T → CPoly}
    (hj : MetricWaveJetFamily G b s a bb H m J phi A)
    (S : T → Coord → ℝ) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ᶠ N : ℝ in atTop, ∀ t, ∀ x : Coord, ‖x‖ ≤ 2*N^(-1/3:ℝ) →
      (reval (phi t) x).re-S t x ≤ -c*‖x‖^2)
    (K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t, ∀ x : Coord,
      DerivativeBound k0 (fun z ↦ smoothSecondOrder (G t) (b t)
        (fun w ↦ Yau.Waves.scaledCutoff N (0:Coord) w •
          (finiteAmplitude (fun j ↦ A j t) J N w * waveExp (reval (phi t)) N w)) z +
        ((4:ℂ)*(N:ℂ)^2+6*(N:ℂ)) * (Yau.Waves.scaledCutoff N (0:Coord) z •
          (finiteAmplitude (fun j ↦ A j t) J N z * waveExp (reval (phi t)) N z))) x
        (C*N^(-(K:ℝ))*Real.exp (N*S t x)) := by
  have hGb (i j : Fin 4) := uniformSmoothBounded_of_continuous_derivatives univ isCompact_univ 2
    (fun t ↦ G t i j) (fun t ↦ hG.principal_smooth t i j) (fun k ↦ hG.principal_jets k i j)
  have hbb (j : Fin 4) := uniformSmoothBounded_of_continuous_derivatives univ isCompact_univ 2
    (fun t ↦ b t j) (fun t ↦ hG.drift_smooth t j) (fun k ↦ hG.drift_jets k j)
  obtain ⟨C,hC,hbound⟩ := global_uniform_cutoff_wave_residual isCompact_univ c hc G b hGb hbb
    hG.principal_symm phi A hj.phase_continuous hj.amplitude_continuous m J K k0 hm hJ
    (fun t _ ↦ hj.eikonal_flat t) (fun t _ ↦ hj.transport_zero t)
    (fun j hj' t _ ↦ hj.transport_next j hj' t) S
    (hgap.mono (fun _ h t _ ↦ h t))
  exact ⟨C,hC,hbound.mono (fun _ h t ↦ h t (mem_univ t))⟩

end
end Yau.Geometry

end OAI

import OAI.Geometry.NodalSets.Waves.TripleWaveParameters
import OAI.Geometry.NodalSets.Waves.WitnessedEuclideanWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

abbrev SourceFrameTriple (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (y : T → Coord) := AdmissibleFrameTriple (g ∘ y) (sourceHessian g S ∘ y) (metricGradient g S ∘ y)

def sourceTripleAlpha (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (y : T → Coord) (z : T × Fin 3) : ℝ :=
  Real.sqrt (g (y z.1) (metricGradient g S (y z.1)) (metricGradient g S (y z.1)))

def sourceTripleBeta (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S : Coord → ℝ)
    (y : T → Coord) (z : T × Fin 3) : ℝ :=
  Real.sqrt (g (y z.1) (metricGradient g S (y z.1)) (metricGradient g S (y z.1))+4)

structure TripleSourceWaveData
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w S : Coord → ℝ)
    (y : T → Coord) (d : SourceFrameTriple g S y) (m J K k0 : ℕ) where
  beta : ContDiffBump (0:Coord)
  phi : T × Fin 3 → CPoly
  A : ℕ → T × Fin 3 → CPoly
  F : T × Fin 3 → OpenPartialHomeomorph Coord Coord
  c : ℝ
  Cw : ℝ
  Cr : ℝ
  R : ℝ
  c_pos : 0 < c
  Cw_pos : 0 < Cw
  Cr_pos : 0 < Cr
  R_pos : 0 < R
  sourceRadius : ℝ
  targetRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  targetRadius_pos : 0 < targetRadius
  jets : MetricWaveJetFamily (extendedPrincipal g (fun z ↦ y z.1) d.frame beta)
    (extendedDrift g w (fun z ↦ y z.1) d.frame beta)
    (fun z ↦ S (y z.1)) (sourceTripleAlpha g S y) (sourceTripleBeta g S y)
    (fun z ↦ envelopeHessian (S ∘ actualMetricChart g (y z.1) (d.frame z))) m J phi A
  chart_eq : ∀ z, (F z : Coord → Coord) = actualMetricChart g (y z.1) (d.frame z)
  chart_domain : ∀ z, (F z).source = Metric.ball 0 sourceRadius ∧
    Metric.closedBall (y z.1) targetRadius ⊆ (F z).target ∧
    ContDiffOn ℝ ∞ (F z).symm (F z).target
  estimates : ∀ᶠ n : ℕ in atTop, ∀ t,
    let V := chartPushforward (F t) (coordinateWave phi A J (n:ℝ) t)
    ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
    tsupport V ⊆ {z | sourceEuclideanNorm (z-y t.1) ≤ R*(n:ℝ)^(-1/3:ℝ)} ∧
    ∀ z : Coord,
      (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val V z‖ ≤
        Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-c*(n:ℝ)*(sourceEuclideanNorm (z-y t.1))^2)) ∧
      DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w V z +
        ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*V z) z
          (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z))

theorem construct_triple_source_waves
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → Coord) (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (d : SourceFrameTriple g S y) {U : Set Coord} (hU : IsOpen U)
    (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
    (m J K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    Nonempty (TripleSourceWaveData g w S y d m J K k0) := by
  have hp : Continuous (fun z : T × Fin 3 ↦ metricGradient g S (y z.1)) := (metricGradient_continuous g hg hpos S hS).comp (hy.comp continuous_fst)
  have hlen : Continuous (fun z : T × Fin 3 ↦
      g (y z.1) (metricGradient g S (y z.1)) (metricGradient g S (y z.1))) :=
    (((hg.continuous.comp (hy.comp continuous_fst)).clm_apply hp).clm_apply hp)
  have hapos (z : T × Fin 3) : 0 < sourceTripleAlpha g S y z :=
    Real.sqrt_pos.mpr (hpos (y z.1) _ (hp0 z.1))
  have hbpos (z : T × Fin 3) : 0 < sourceTripleBeta g S y z := by
    apply Real.sqrt_pos.mpr
    have h := hpos (y z.1) _ (hp0 z.1)
    linarith
  have hab (z : T × Fin 3) : (sourceTripleBeta g S y z)^2 = (sourceTripleAlpha g S y z)^2+4 := by
    dsimp [sourceTripleAlpha,sourceTripleBeta]
    rw [Real.sq_sqrt (hpos (y z.1) _ (hp0 z.1)).le,Real.sq_sqrt]
    have h := hpos (y z.1) _ (hp0 z.1)
    linarith
  obtain ⟨beta,phi,A,F,c,Cw,Cr,R,r,delta,hc,hCw,hCr,hR,hr,hdelta,hjets,hF,hdom,hest⟩ :=
    witnessed_source_wave_estimates_euclidean g hg hs hpos w hw S hS
      (fun z : T × Fin 3 ↦ y z.1) (hy.comp continuous_fst) d.frame d.continuous_frame
      d.frame_orthonormal hU (fun z ↦ hyU z.1) hwpos (fun z ↦ d.q z.1 z.2)
      (sourceTripleAlpha g S y) (sourceTripleBeta g S y) hlen.sqrt (hlen.add continuous_const).sqrt
      (fun z ↦ ne_of_gt (hapos z)) (fun z ↦ ne_of_gt (hbpos z)) hab
      (d.frame_first (fun t ↦ hpos (y t)) hp0) (d.frame_second (fun t ↦ hpos (y t)) hp0)
      (fun z ↦ d.strict z.1 z.2) m J K k0 hm hJ
  exact ⟨⟨beta,phi,A,F,c,Cw,Cr,R,hc,hCw,hCr,hR,r,delta,hr,hdelta,hjets,hF,hdom,hest⟩⟩

end
end Yau.Geometry

end OAI

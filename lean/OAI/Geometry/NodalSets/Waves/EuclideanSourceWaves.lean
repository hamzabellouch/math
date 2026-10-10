import OAI.Geometry.NodalSets.Elliptic.CoordinateNorm
import OAI.Geometry.NodalSets.Waves.ConstructedSourceWavesLemmas

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter Set
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem constructed_source_wave_estimates_euclidean
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
      sourceHessian g S (y t) (q t) (q t)) (m J : ℕ) (K k0 : ℕ) (hm : 3*K+4*k0+6 < m+1) (hJ : K+k0+1 ≤ J) :
    ∃ (beta : ContDiffBump (0:Coord)) (phi : T → CPoly) (A : ℕ → T → CPoly)
      (F : T → OpenPartialHomeomorph Coord Coord) (c Cw Cr R : ℝ),
      0 < c ∧ 0 < Cw ∧ 0 < Cr ∧ 0 < R ∧
      MetricWaveJetFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta)
        (fun t ↦ S (y t)) a bb
        (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) m J phi A ∧
      (∀ t, (F t : Coord → Coord) = actualMetricChart g (y t) (e t)) ∧
      ∀ᶠ n : ℕ in atTop, ∀ t,
        let V := chartPushforward (F t) (coordinateWave phi A J (n:ℝ) t)
        ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
        tsupport V ⊆ {z | sourceEuclideanNorm (z-y t) ≤ R*(n:ℝ)^(-1/3:ℝ)} ∧
        ∀ z : Coord,
          (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val V z‖ ≤
            Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-c*(n:ℝ)*(sourceEuclideanNorm (z-y t))^2)) ∧
          DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w V z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*V z) z
              (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z)) := by
  obtain ⟨beta,phi,A,F,c,Cw,Cr,R,hc,hCw,hCr,hR,hjets,hFe,hest⟩ := constructed_source_wave_estimates
    g hg hs hpos w hw S hS y hy e he ho hU hyU hwpos q a bb ha hbb ha0 hb0 hlen hap hbq hstrict
    m J K k0 hm hJ
  refine ⟨beta,phi,A,F,c/4,Cw,Cr,2*R,by positivity,hCw,hCr,by positivity,hjets,hFe,?_⟩
  filter_upwards [hest] with n hn
  intro t
  obtain ⟨hsm,hcomp,hsup,hbounds⟩ := hn t
  refine ⟨hsm,hcomp,?_,?_⟩
  · intro z hz
    have hzsup : ‖z-y t‖ ≤ R*(n:ℝ)^(-1/3:ℝ) := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hsup hz
    calc
      _ ≤ 2*‖z-y t‖ := sourceEuclideanNorm_le _
      _ ≤ 2*(R*(n:ℝ)^(-1/3:ℝ)) := mul_le_mul_of_nonneg_left hzsup (by norm_num)
      _ = _ := by ring
  · intro z
    refine ⟨?_,(hbounds z).2⟩
    intro k
    apply ((hbounds z).1 k).trans
    have he := gaussian_source_euclidean (z-y t) c (n:ℝ) (S z) hc.le (by positivity)
    exact mul_le_mul_of_nonneg_left he (by positivity)

end
end Yau.Geometry

end OAI

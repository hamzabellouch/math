import OAI.Geometry.NodalSets.Charts.SphereChartL2Comparison
import OAI.Geometry.NodalSets.Coefficients.IntrinsicDivergenceCoefficients
import OAI.Geometry.NodalSets.Elliptic.RealEllipticLocalCompactness

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem sphere_normalized_chart_subsequence (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
    (hA : ∀ t, IntrinsicTensorSmooth (A t))
    (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
    (hr : ∀ t, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (rho t)) (hrp : ∀ t p, 0 < rho t p)
    (hrjoint : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (lam : ℝ) (p : Base)
    (hCjoint : ∀ i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
    (hVjoint : ∀ ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
    (t : ℕ → T) (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j q z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) q z =
      lam*w j ((extChartAt (𝓡 4) q).symm z))
    (hn : ∀ j, sphereWeightedPairing (rho (t j)) (w j) (w j)=1) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
      (∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
          (partialJet v ds) atTop Q) ∧
      (∀ n (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
          (iteratedFDeriv ℝ n v) atTop Q) := by
  apply real_elliptic_local_subsequence
    (fun t ↦ intrinsicDivergencePrincipal (A t) p)
    (fun t ↦ intrinsicDivergencePotential (rho t) lam p)
    (fun t ↦ intrinsicDivergencePrincipal_smooth (A t) (hA t) (hs t) (hp t) p)
    (fun t ↦ intrinsicDivergencePotential_smooth (rho t) (hr t) lam p)
    (fun t ↦ intrinsicDivergencePrincipal_symmetric (A t) (hs t) p)
    (fun t ↦ intrinsicDivergencePrincipal_posDef (A t) (hs t) (hp t) p)
    hCjoint hVjoint t (fun j ↦ w j ∘ sphereChartCoordMap p)
    (fun j ↦ spherePullback_smooth (w j) (hw j) p)
    (fun j ↦ intrinsic_unweighted_divergence_equation (A (t j)) (rho (t j)) (hrp (t j)) (w j) lam (he j) p)
  intro R
  obtain ⟨K,hK,hbound⟩ := sphere_normalized_chart_l2_bound rho hrjoint hrp p
    (closedBall (0 : Yau.Jets.Coord) ((R:ℝ)+2)) (isCompact_closedBall _ _)
  exact ⟨K,hK.le,fun j ↦ hbound (t j) (w j) (hw j).continuous (hn j)⟩

end
end Yau.Target

end OAI

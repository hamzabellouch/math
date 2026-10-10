import OAI.Geometry.NodalSets.Charts.SphereChartEllipticCompactness
import OAI.Geometry.NodalSets.Elliptic.FiniteSubsequenceSelection

namespace OAI

namespace Yau.Target
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem sphere_finite_atlas_subsequence (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
    (hA : ∀ t, IntrinsicTensorSmooth (A t))
    (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
    (hr : ∀ t, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (rho t)) (hrp : ∀ t p, 0 < rho t p)
    (hrjoint : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (lam : ℝ)
    (hCjoint : ∀ p i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
    (hVjoint : ∀ p ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
    (t : ℕ → T) (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j q z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) q z =
      lam*w j ((extChartAt (𝓡 4) q).symm z))
    (hn : ∀ j, sphereWeightedPairing (rho (t j)) (w j) (w j)=1) (P : Finset Base) :
    ∃ nu : ℕ → ℕ, StrictMono nu ∧ ∀ p ∈ P,
      ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧
        (∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
            (partialJet v ds) atTop Q) ∧
        (∀ n (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
            (iteratedFDeriv ℝ n v) atTop Q) := by
  apply finite_subsequence_selection P
  · intro p nu hnu
    obtain ⟨v,hv,mu,hmu,hpartial,hderiv⟩ := sphere_normalized_chart_subsequence
      A rho hA hs hp hr hrp hrjoint lam p (hCjoint p) (hVjoint p)
      (t ∘ nu) (w ∘ nu) (fun j ↦ hw (nu j)) (fun j ↦ he (nu j)) (fun j ↦ hn (nu j))
    exact ⟨mu,hmu,v,hv,hpartial,hderiv⟩
  · intro p nu mu hR hmu
    obtain ⟨v,hv,hpartial,hderiv⟩ := hR
    exact ⟨v,hv,fun ds Q hQ ↦ (hpartial ds Q hQ).seq_tendstoUniformlyOn mu hmu.tendsto_atTop,
      fun n Q hQ ↦ (hderiv n Q hQ).seq_tendstoUniformlyOn mu hmu.tendsto_atTop⟩

end
end Yau.Target

end OAI

import Mathlib
import OAI.Analysis.AffineBernstein.SigmaBaseTransport
import OAI.Analysis.AffineBernstein.SigmaNormalization

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section NormalizedSigmaTransport
open Filter Metric

lemma affineEpigraphPullback_normalize {n k m : ℕ} (Ω : Set (Space n)) (u : Space n → ℝ)
    (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    (N : (Space k × Space m) ≃L[ℝ] (Space k × Space m)) :
    affineEpigraphPullback Ω u a (N.symm.trans L) = N '' affineEpigraphPullback Ω u a L := by
  ext q
  constructor
  · intro h
    exact ⟨N.symm q,h,N.apply_symm_apply q⟩
  · rintro ⟨p,hp,rfl⟩
    simpa only [affineEpigraphPullback,Set.mem_ofPred_eq,ContinuousLinearEquiv.trans_apply,
      N.symm_apply_apply] using hp

/-- Actual sigma in any diagonal-base/transverse GL normalization. All support
smoothness and determinant positivity are produced by the positive Hessian of
the original graph, not assumed as sigma identities. -/
theorem affineEpigraph_sigma_normalization {n k m d : ℕ} (hm : 1 ≤ m)
    (hn : n = k+d) (bE : OrthonormalBasis (Fin d ⊕ Unit) ℝ (Space m))
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    (B : Space k ≃L[ℝ] Space k) (A : Space m ≃L[ℝ] Space m)
    (coeff : Fin k → ℝ) (hcoeff : ∀ i, coeff i ≠ 0) (hB : ∀ s i, B s i = coeff i*s i)
    {D : Set (Space k)} (hD : IsOpen D)
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : B '' Q ⊆ D)
    (hs : ∀ s ∈ Q, ∀ i, s i ≠ 0)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈
      affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)})
    (hzero : ∀ s ∈ D, (0 : Space m) ∈ interior {y | (s,y) ∈
      affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)}) :
    let H := fun q : Space k × Space m =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let H' := fun q : Space k × Space m => homogeneousSupport {y | (q.1,y) ∈
      affineEpigraphPullback Ω u a ((B.prodCongr A).symm.trans L)} q.2
    let bS := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
      ENNReal.ofReal (tubeMeasureDensity n H bS bE (q.1,q.2)*tubeLogMassWeight H (q.1,q.2))
      ∂(volume.restrict Q).prod (volume : Measure (Space m)).toSphere) =
    (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
      ENNReal.ofReal (tubeMeasureDensity n H' bS bE (q.1,q.2)*tubeLogMassWeight H' (q.1,q.2))
      ∂(volume.restrict (B '' Q)).prod (volume : Measure (Space m)).toSphere) := by
  let : NeZero m := ⟨by omega⟩
  let L' := (B.prodCongr A).symm.trans L
  let K := fun s : Space k => {y | (s,y) ∈ affineEpigraphPullback Ω u a L'}
  let H' := fun q : Space k × Space m => homogeneousSupport (K q.1) q.2
  have hh (s : Space k) (hsD : s ∈ D) (e : Space m) (he : e ≠ 0) :
      ContDiffAt ℝ ∞ H' (s,e) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L' hD hK hzero hsD he).1
  have hrad (s : Space k) (hsD : s ∈ D) (e : Space m) (he : e ≠ 0) :=
    affineEpigraph_support_radial hΩ hcv hu hp a L' hD hK hzero hsD he
  have hpos (s : Space k) (hsD : s ∈ D) (e : Space m) (he : e ≠ 0) :=
    affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L' hD hK hzero hsD he
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis bE
  have ht := sigma_cell_linear_comp bE B (adjointEquiv A.symm) coeff hcoeff hB hD hQ hQD
    hK (fun s hs => ⟨0,interior_subset (hzero s hs)⟩) hs hh hrad
    (fun s hs e he => ⟨(hpos s hs e he).2.2,(hpos s hs e he).1.det_pos,(hpos s hs e he).2.1⟩)
  have heq : (fun q : Space k × Space m => H' (B q.1,adjointEquiv A.symm q.2)) =
      (fun q : Space k × Space m =>
        homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2) := by
    dsimp only [H',K,L']
    rw [affineEpigraphPullback_normalize]
    exact support_normalized_pullback B A _
  dsimp only at ht ⊢
  rw [heq] at ht
  simpa only [hn,H',K,L'] using ht
end NormalizedSigmaTransport


end AffineBernstein
end

end OAI

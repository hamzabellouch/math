import Mathlib
import OAI.Analysis.AffineBernstein.ActualProjectiveDensity
import OAI.Analysis.AffineBernstein.ProjectiveInverseWeight

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- Actual degree-zero inverse metric weight and projective affine density
combined. This is the normalized integrand required in the inverse-cap
estimate, derived solely from the true affine epigraph support. -/
theorem affineEpigraph_projective_inverseArea_density {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : ‖e‖ = 1)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {c : ℝ} (hc : 0 < c) (hflat : inner ℝ (c • e) (bE (Sum.inr ())) = 1)
    (v w : ι → ℝ) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    tubeAreaDensity (tubeBaseMatrix H (s,c • e) bS) (tubeRadiusMatrix H (s,c • e) bE) δ *
      (‖supportConormal H (s,c • e)‖ * inverseMatrixPair (tubeBaseMatrix H (s,c • e) bS) v w) =
      Real.rpow c (-((Fintype.card κ:ℝ)+1)) *
        ((Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
          Real.rpow (tubeAngularDensity H (s,e) bE) (1-δ)) *
        (‖supportConormal H (s,e)‖ * inverseMatrixPair (tubeBaseMatrix H (s,e) bS) v w)) := by
  have he0 : e ≠ 0 := by intro heq; simp [heq] at he
  have hce : c • e ≠ 0 := smul_ne_zero hc.ne' he0
  have hj := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he0).1
  have hjc := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs hce).1
  have hB := (affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs he0 bS bE).1
  dsimp only
  rw [affineEpigraph_projective_area_density hΩ hcv hu hp a L hD hK hzero hs he bS bE hc hflat,
    homogeneous_inverseMetricWeight_scale hD hs hK
      (fun s hs => ⟨0,interior_subset (hzero s hs)⟩) hc hj hjc bS hB.det_pos.ne']
  ring

end AffineBernstein
end

end OAI

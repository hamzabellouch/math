import Mathlib
import OAI.Analysis.AffineBernstein.ActualInvariantTube
import OAI.Analysis.AffineBernstein.ProjectiveDensity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

section ActualProjectiveDensity
open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- Exact flat/spherical density normalization for the genuine epigraph support.
There are no assumed homogeneity or radial-Hessian identities here. -/
theorem affineEpigraph_projective_area_density {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : ‖e‖ = 1)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {c : ℝ} (hc : 0 < c) (hflat : inner ℝ (c • e) (bE (Sum.inr ())) = 1) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    tubeAreaDensity (tubeBaseMatrix H (s,c • e) bS) (tubeRadiusMatrix H (s,c • e) bE) δ =
      Real.rpow c (-((Fintype.card κ:ℝ)+1)) *
        (Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
          Real.rpow (tubeAngularDensity H (s,e) bE) (1-δ)) := by
  have he0 : e ≠ 0 := by intro heq; simp [heq] at he
  have hce : c • e ≠ 0 := smul_ne_zero hc.ne' he0
  have hp' := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs he0 bS bE
  exact homogeneous_projective_area_density hD hs hK
    (fun s hs => ⟨0,interior_subset (hzero s hs)⟩) hc he
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he0).1
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs hce).1 bS bE hflat
    (fun v => affineEpigraph_support_radial hΩ hcv hu hp a L hD hK hzero hs hce v)
    hp'.1.det_pos.le hp'.2.1.le

end ActualProjectiveDensity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Cauchy--Schwarz for a positive definite inverse matrix, including zero vectors. -/

end AffineBernstein
end

end OAI

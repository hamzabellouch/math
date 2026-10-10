import Mathlib
import OAI.Analysis.AffineBernstein.ActualAmbientFEquation
import OAI.Analysis.AffineBernstein.RoundSliceContractions

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/- The coordinate-free round-sphere f-equation for the actual affine epigraph.
All analytic and cofactor terms are the genuine support objects; no tube PDE is assumed. -/
theorem affineMaximal_round_tube_f_equation {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (hm : AffineMaximalOn Ω u)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : ‖e‖ = 1)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let q := (s,e)
    let B := tubeBaseMatrix H q bS
    let Q := tubeAngularDensity H q bE
    let V := fun i : ι => ((bS i), (0:E))
    let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
    let F := invariantTubeF H bS bE δ
    let P := fun y => Real.log (H y)
    let T := fun y => F y+P y
    let N := supportNewtonTensor bE (fun y => H (s,y))
    let dF := tangentProjection e (gradient (fun y => F (s,y)) e)
    let dP := tangentProjection e (gradient (fun y => P (s,y)) e)
    (n : ℝ) - 2*Fintype.card ι + H q*flatInverseTrace B V F q -
      H q*flatInversePair B V P P q -
      ((n : ℝ)+1)*H q*flatInversePair B V T T q +
      H q/Q * roundHessianContraction bE N (fun y => F (s,y)) e +
      2*H q/Q * N e dP dF + H q/Q * N e dF dF = 0 := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  let δ : ℝ := 1/((Fintype.card ι : ℝ)+Fintype.card κ+2)
  let F := invariantTubeF H bS bE δ
  let P := fun y => Real.log (H y)
  have hen : e ≠ 0 := by intro hz; simp [hz] at he
  obtain ⟨c,hc⟩ := exists_orthonormalBasis_last bE he
  have hH : ContDiffAt ℝ ∞ H (s,e) := (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs hen).1
  have hpos := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs hen bS bE
  have hF : ContDiffAt ℝ ∞ F (s,e) := affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hs hen bS bE δ
  have hP : ContDiffAt ℝ ∞ P (s,e) := hH.log hpos.2.2.ne'
  have hr : ∀ v, fderiv ℝ (fderiv ℝ H) (s,e) (0,v) (0,e) = 0 :=
    affineEpigraph_support_radial hΩ hcv hu hp a L hD hK hzero hs hen
  have hQ : tubeAngularDensity H (s,e) bE = (tubeRadiusMatrix H (s,e) c).det := by
    rw [← tubeAngularDensity_basis_independent H (s,e) bE c,tubeAngularDensity_of_last_null hH c]
    intro v
    rw [hc]
    exact hr v
  have hR : (tubeRadiusMatrix H (s,e) c).det ≠ 0 := by
    rw [← hQ]
    exact hpos.2.1.ne'
  have hFr : fderiv ℝ F (s,e) (0,e) = 0 :=
    affineEpigraph_invariant_f_radial hΩ hcv hu hp a L hD hK hzero hs hen bS bE
  have htrace := supportNewtonTrace_slice bE c hH hc hr hR hF hFr
  have hpair := supportNewtonPair_slice bE c hH hc hr hR
    (hP.differentiableAt (by simp)) (hF.differentiableAt (by simp))
  have hsquare := supportNewtonPair_slice bE c hH hc hr hR
    (hF.differentiableAt (by simp)) (hF.differentiableAt (by simp))
  have hh := affineMaximal_invariant_tube_f_equation hΩ hcv hu hp hm a L hD hK hzero hs bS c hc
  dsimp only at hh
  have hFc : invariantTubeF H bS c δ = F := funext (invariantTubeF_basis_independent H bS bE c δ)
  change (n : ℝ)-2*Fintype.card ι + H (s,e)*flatInverseTrace (tubeBaseMatrix H (s,e) bS)
      (fun i => (bS i,0)) F (s,e) - H (s,e)*flatInversePair (tubeBaseMatrix H (s,e) bS)
      (fun i => (bS i,0)) P P (s,e) - ((n : ℝ)+1)*H (s,e)*flatInversePair (tubeBaseMatrix H (s,e) bS)
      (fun i => (bS i,0)) (fun y => F y+P y) (fun y => F y+P y) (s,e) +
      H (s,e)/tubeAngularDensity H (s,e) bE * roundHessianContraction bE
        (supportNewtonTensor bE (fun y => H (s,y))) (fun y => F (s,y)) e +
      2*H (s,e)/tubeAngularDensity H (s,e) bE * supportNewtonTensor bE (fun y => H (s,y)) e
        (tangentProjection e (gradient (fun y => P (s,y)) e))
        (tangentProjection e (gradient (fun y => F (s,y)) e)) +
      H (s,e)/tubeAngularDensity H (s,e) bE * supportNewtonTensor bE (fun y => H (s,y)) e
        (tangentProjection e (gradient (fun y => F (s,y)) e))
        (tangentProjection e (gradient (fun y => F (s,y)) e)) = 0
  rw [htrace,hpair,hsquare,hQ]
  simp only [← mul_assoc,div_mul_cancel₀ _ hR]
  rw [hFc] at hh
  convert hh using 1

end AffineBernstein
end

end OAI

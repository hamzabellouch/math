import Mathlib
import OAI.Analysis.AffineBernstein.ActualInvariantTube
import OAI.Analysis.AffineBernstein.BaseExponentialIBP

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma affineEpigraph_tube_base_smooth {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {e : E} (he : e ≠ 0)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun q => Real.log (H q)
    let F := invariantTubeF H bS bE δ
    ContDiffOn ℝ ∞ (fun s => H (s,e)) D ∧
    ContDiffOn ℝ ∞ (fun s => P (s,e)) D ∧
    ContDiffOn ℝ ∞ (fun s => F (s,e)) D := by
  dsimp only
  let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
  have hH (s : S) (hs : s ∈ D) : ContDiffAt ℝ ∞ H (s,e) :=
    (affineEpigraph_support_jets hΩ hcv hu hp a L hD hK hzero hs he).1
  refine ⟨?_,?_,?_⟩
  · intro s hs
    exact ((hH s hs).comp s (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  · intro s hs
    have hp' := affineEpigraph_invariant_tube_positive hΩ hcv hu hp a L hD hK hzero hs he bS bE
    exact (((hH s hs).log hp'.2.2.ne').comp s (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt
  · intro s hs
    exact ((affineEpigraph_invariant_f_smooth hΩ hcv hu hp a L hD hK hzero hs he bS bE δ).comp s
      (contDiffAt_id.prodMk contDiffAt_const)).contDiffWithinAt

variable [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  {μ : Measure S} [μ.IsAddHaarMeasure]

/- Actual base cofactor identity for either f, log h, or any smooth tube
scalar. The derivative coefficients are the Hessian cofactors of the literal
support function, and the exponential is the exact invariant measure weight. -/
theorem affineEpigraph_base_weighted_ibp {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {e : E} (he : e ≠ 0)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    {σ g : S → ℝ} (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ)
    (hσD : tsupport σ ⊆ D) (hg : ContDiffOn ℝ ∞ g D) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let P := fun s => Real.log (H (s,e))
    let F := fun s => invariantTubeF H bS bE (1/((Fintype.card ι : ℝ)+Fintype.card κ+2)) (s,e)
    let K := fun s => -H (s,e)
    let c := ((n : ℝ)+2)/2
    let W := fun s => Real.exp (-(n : ℝ)*P s-c*F s)
    (∫ s, W s*σ s^2 * (flatCofactorTrace K bS g s-
      (n : ℝ)*flatCofactorPair K bS P g s-c*flatCofactorPair K bS F g s) ∂μ) =
      -2*(∫ s, W s*σ s*flatCofactorPair K bS σ g s ∂μ) := by
  dsimp only
  have hsmooth := affineEpigraph_tube_base_smooth hΩ hcv hu hp a L hD hK hzero he bS bE
    (1/((Fintype.card ι : ℝ)+Fintype.card κ+2))
  have hh := integral_flatCofactor_exp_square (μ := μ) bS hσ hc
    (fun x hx => (hsmooth.1.contDiffAt (hD.mem_nhds (hσD hx))).neg)
    (fun x hx => hsmooth.2.1.contDiffAt (hD.mem_nhds (hσD hx)))
    (fun x hx => hsmooth.2.2.contDiffAt (hD.mem_nhds (hσD hx)))
    (fun x hx => hg.contDiffAt (hD.mem_nhds (hσD hx))) (-(n : ℝ)) (-(((n : ℝ)+2)/2))
  simpa only [neg_mul,sub_eq_add_neg] using hh

end AffineBernstein
end

end OAI

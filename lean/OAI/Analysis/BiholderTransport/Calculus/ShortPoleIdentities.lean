import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.ShortForward

namespace OAI



noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

omit [CompactSpace M] [Nonempty M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] [CompleteSpace P] in
lemma short_family_first_jet_limit {a : M} {ψ : P×Model n → ℝ}
    {p : P} {x : Model n} {B : (P×ℝ)×Model n → Model n} {U : (P×ℝ)×Model n → ℝ}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target)
    (hU : ContDiffAt ℝ ∞ U ((p,0),x))
    (hZB : ∀ᶠ q in 𝓝 ((p,0),x),B (q.1,parametricShortForward a ψ q)=q.2)
    (hUE : ∀ q,U q=ψ (q.1.1,B q)+q.1.2*parametricShortEnergy a ψ (q.1.1,B q)) :
    Tendsto (fun q : (P×ℝ)×Model n => fderiv ℝ (fun w => U (q.1,w)) q.2)
      (𝓝 ((p,0),x)) (𝓝 (fderiv ℝ (fun w => ψ (p,w)) x)) := by
  have hi : ContinuousAt (fun w : Model n => ((p,(0:ℝ)),w)) x :=
    continuousAt_const.prodMk continuousAt_id
  have hz := hi.eventually hZB
  have heq : (fun w => U ((p,0),w))=ᶠ[𝓝 x] (fun w => ψ (p,w)) := by
    filter_upwards [hz,(isOpen_extChartAt_target a).mem_nhds hx] with w hw hwc
    change B ((p,0),shortForward a (fun v => ψ (p,v)) (0,w))=w at hw
    rw [shortForward_zero hwc] at hw
    rw [hUE,hw]
    simp only [zero_mul,add_zero]
  have H := (ContDiffAt.partial_snd_fderiv (f := fun q w => U (q,w)) hU).continuousAt.tendsto
  rw [heq.fderiv_eq] at H
  exact H

end WeakMTWTransport

end

end OAI

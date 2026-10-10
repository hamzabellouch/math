import Mathlib
import OAI.Analysis.BiholderTransport.Contact.CoordinateScalarSupport

namespace OAI



noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

def jointScalarSupport (a : M) (Φ : P×ℝ → ℝ)
    (q : (P×((ℝ×ℝ)×(Model n×Model n)))×Model n) : ℝ :=
  Φ (q.1.1,coordinateScalarSupport a id (q.1.2,q.2))

omit [Nonempty M] [CompleteSpace P] in
lemma jointScalarSupport_contDiffAt {a : M} {b p : Model n} {v s : ℝ}
    {param : P} {Φ : P×ℝ → ℝ}
    (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target) (hs : s≠0)
    (hp : s • (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) p∈
        injectivityDomain ((extChartAt 𝓘(ℝ,Model n) a).symm b))
    (hΦ : ContDiffAt ℝ ∞ Φ (param,v)) :
    ContDiffAt ℝ ∞ (jointScalarSupport a Φ) ((param,((v,s),(b,p))),b) := by
  have hF := (coordinateScalarSupport_contDiffAt hb hs hp contDiffAt_id).comp
    ((param,((v,s),(b,p))),b) (contDiffAt_fst.snd.prodMk contDiffAt_snd)
  have hpair := contDiffAt_fst.fst.prodMk hF
  exact (show ContDiffAt ℝ ∞ Φ
    (param,coordinateScalarSupport a id (((v,s),(b,p)),b)) from by
      simpa only [coordinateScalarSupport_self,id_eq] using hΦ).comp
        (f := fun q : (P×((ℝ×ℝ)×(Model n×Model n)))×Model n =>
          (q.1.1,coordinateScalarSupport a id (q.1.2,q.2))) _ hpair
end WeakMTWTransport

end

end OAI

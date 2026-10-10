import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.CostSmooth
import OAI.Analysis.BiholderTransport.Coordinates.ChartCostJets

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

omit [Nonempty M] in
lemma chartCost_pair_contDiffAt_diagonal {a : M} {x : Model n}
    (hx : x∈(extChartAt 𝓘(ℝ,Model n) a).target) :
    ContDiffAt ℝ ∞ (fun q : Model n×Model n =>
      chartCost a ((extChartAt 𝓘(ℝ,Model n) a).symm q.1) q.2) (x,x) := by
  let χ := extChartAt 𝓘(ℝ,Model n) a
  have hi : ContMDiffAt 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) ∞ χ.symm x :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hx)
  have hc := cost_contMDiffAt_of_injectivityDomain
    (⟨χ.symm x,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
    (zero_mem_injectivityDomain (n := n) (χ.symm x))
  simp only [riemannianExp_zero] at hc
  exact (hc.comp (x,x) ((hi.comp (x,x) contDiffAt_snd.contMDiffAt).prodMk
    (hi.comp (x,x) contDiffAt_fst.contMDiffAt))).contDiffAt
end WeakMTWTransport

end

end OAI

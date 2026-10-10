import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.InjectivityOpen
import OAI.Analysis.BiholderTransport.Regularity.InteriorCompactUniqueFiber
import OAI.Analysis.BiholderTransport.Coordinates.BranchInverse

namespace OAI

section

section

noncomputable section
open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Pointwise

namespace WeakMTWTransport
section FirstNonconjugate
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma mem_injectivityDomain_of_unique_nonconjugate {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hu : ∀ q∈minimizingVectors x, riemannianExp x q=riemannianExp x p → q=p)
    (hreg : Function.Injective (fderiv ℝ (fun q => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x q)) p)) :
    p∈injectivityDomain x := by
  obtain ⟨P,_,_,hleft,_⟩ := exists_smooth_exp_branch
    (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) hreg
  have hmap := (FiberBundle.continuous_totalSpaceMk (Model n)
    (fun a : M => TangentSpace 𝓘(ℝ,Model n) a) x).continuousAt.eventually hleft
  obtain ⟨U,hUsub,hU,hpU⟩ := mem_nhds_iff.mp hmap
  apply interior_minimizingVectors_subset x
  apply interior_of_compact_unique_fiber (isCompact_minimizingVectors x)
    (continuous_riemannianExp x) (exists_minimizing_vector (n := n) x) hu
  refine ⟨U,hU,hpU,?_⟩
  intro q hq r hr he
  have hq' := hUsub hq
  have hr' := hUsub hr
  change P (x,riemannianExp x q)=⟨x,q⟩ at hq'
  change P (x,riemannianExp x r)=⟨x,r⟩ at hr'
  exact TotalSpace.mk_injective x (hq'.symm.trans ((congrArg (fun y => P (x,y)) he).trans hr'))

end FirstNonconjugate
end WeakMTWTransport

end

end

end

end OAI

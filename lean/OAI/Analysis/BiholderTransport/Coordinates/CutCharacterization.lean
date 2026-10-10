import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.InjectivityOpen
import OAI.Analysis.BiholderTransport.Regularity.InteriorCompactUniqueFiber
import OAI.Analysis.BiholderTransport.Coordinates.BranchInverse

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma joint_exp_locally_injective_of_nonconjugate (z : TangentBundle 𝓘(ℝ,Model n) M)
    (hz : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp z.1 z.2) (riemannianExp z.1 v)) z.2)) :
    ∃ U : Set (TangentBundle 𝓘(ℝ,Model n) M), IsOpen U ∧ z ∈ U ∧
      InjOn (fun q : TangentBundle 𝓘(ℝ,Model n) M => (q.1,riemannianExp q.1 q.2)) U := by
  obtain ⟨P,_,_,hleft,_⟩ := exists_smooth_exp_branch z hz
  obtain ⟨U,hUP,hU,hzU⟩ := mem_nhds_iff.mp hleft
  refine ⟨U,hU,hzU,?_⟩
  exact (show LeftInvOn P
    (fun point : TangentBundle 𝓘(ℝ,Model n) M =>
      (point.1,riemannianExp point.1 point.2)) U from hUP).injOn

lemma mem_injectivityDomain_of_nonconjugate_unique {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p))
    (hu : ∀ q ∈ minimizingVectors x, riemannianExp x q=riemannianExp x p → q=p) :
    p ∈ injectivityDomain x := by
  apply interior_minimizingVectors_subset x
  apply interior_of_compact_unique_fiber (isCompact_minimizingVectors x)
    (continuous_riemannianExp x) (exists_minimizing_vector x) hu
  obtain ⟨U,hU,hpU,hinj⟩ := joint_exp_locally_injective_of_nonconjugate ⟨x,p⟩ hp
  let I := fun q : TangentSpace 𝓘(ℝ,Model n) x => (⟨x,q⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  have hI : Continuous I := FiberBundle.continuous_totalSpaceMk (Model n) _ x
  refine ⟨I ⁻¹' U,hU.preimage hI,hpU,?_⟩
  intro a ha b hb he
  exact TotalSpace.mk_injective x (hinj ha hb (Prod.ext rfl he))

end WeakMTWTransport

end

end OAI

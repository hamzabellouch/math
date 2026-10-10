import Mathlib

namespace OAI


noncomputable section
namespace TamingCompatibility.ClosureLinear
open Set
variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
def toClosure (f : E →ₗ[ℝ] F) : E →ₗ[ℝ] f.range.topologicalClosure :=
  f.codRestrict _ (fun x => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self f x))
lemma toClosure_dense (f : E →ₗ[ℝ] F) : DenseRange (toClosure f) := by
  change DenseRange (Set.inclusion (s := Set.range f) (t := closure (Set.range f))
    subset_closure ∘ Set.rangeFactorization f)
  exact ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
    rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)
end TamingCompatibility.ClosureLinear

end

end OAI

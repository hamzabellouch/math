import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {M : Type*} [Mul M]

lemma mem_bicommutant_of_maps_generators (α : M ≃* M) (S : Set M)
    (hα : ∀ x∈S, α x∈S) {a : M} (ha : a∈Set.centralizer (Set.centralizer S)) :
    α a∈Set.centralizer (Set.centralizer S) := by
  intro b hb
  have hb' : α.symm b∈Set.centralizer S := by
    intro x hx
    apply α.injective
    simpa only [map_mul,MulEquiv.apply_symm_apply] using hb (α x) (hα x hx)
  have h := congrArg α (ha (α.symm b) hb')
  simpa only [map_mul,MulEquiv.apply_symm_apply] using h

end Kadison

end

end
end

end OAI

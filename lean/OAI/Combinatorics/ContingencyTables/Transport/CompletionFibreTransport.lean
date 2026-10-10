import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalCompletionFibres

namespace OAI

/-! # Changing a retained profile by an equality keeps the literal views -/

namespace ContingencyTables.PhysicalCompletionFibres

variable {I J : Type*} [Fintype I] [Fintype J]
variable {small : I → J → Bool} {B : I → J → ℕ}
variable {r rbar : I → ℕ} {c cbar : J → ℕ} {z w : SmallProfile small}

def withProfile (h : z=w) (Z : CompletionFibre small B r rbar c cbar z) :
    CompletionFibre small B r rbar c cbar w :=
  ⟨Z.val,by rw [←h]; exact Z.property⟩

lemma withProfile_val (h : z=w) (Z : CompletionFibre small B r rbar c cbar z) :
    (withProfile h Z).val=Z.val := rfl

end ContingencyTables.PhysicalCompletionFibres

end OAI

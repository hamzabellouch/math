import Mathlib

namespace OAI



section
namespace ExactQuantumFactoring
lemma ofFn_val_range (n : ℕ) : (List.ofFn fun i : Fin n => i.val) = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp
end ExactQuantumFactoring

end



end OAI

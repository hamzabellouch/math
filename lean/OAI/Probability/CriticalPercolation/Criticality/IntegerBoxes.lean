import Mathlib

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation

def integerPairBox (k : ℕ) : Set (Multiplicative (ℤ×ℤ)) :=
  {t | |(t.toAdd.1 : ℝ)|≤(k:ℝ) ∧ |(t.toAdd.2 : ℝ)|≤(k:ℝ)}

lemma integerPairBox_finite (k : ℕ) : (integerPairBox k).Finite := by
  have hh := ((Set.finite_Icc (-(k:ℤ)) (k:ℤ)).prod
    (Set.finite_Icc (-(k:ℤ)) (k:ℤ))).image (Multiplicative.ofAdd : ℤ×ℤ → _)
  apply hh.subset
  intro t ht
  refine ⟨t.toAdd,?_,rfl⟩
  have h₁ := abs_le.mp ht.1
  have h₂ := abs_le.mp ht.2
  exact ⟨⟨by exact_mod_cast h₁.1,by exact_mod_cast h₁.2⟩,
    ⟨by exact_mod_cast h₂.1,by exact_mod_cast h₂.2⟩⟩

end CriticalPercolation
end
end
end

end OAI

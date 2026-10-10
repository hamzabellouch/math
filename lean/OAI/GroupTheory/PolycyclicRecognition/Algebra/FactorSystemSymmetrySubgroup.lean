import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemTwist

namespace OAI

/-! # Automorphisms commuting with the section actions and fixing its factors -/

namespace PolycyclicRecognition
variable {N Q : Type} [Group N] [Group Q]

def factorSystemSymmetries (R : NonabelianFactorSystem N Q) : Subgroup (MulAut N) where
  carrier := {A | (∀ q, Commute A (R.action q)) ∧ ∀ q r, A (R.factor q r) = R.factor q r}
  one_mem' := ⟨fun _ => Commute.one_left _, fun _ _ => rfl⟩
  mul_mem' := by
    intro A B hA hB
    refine ⟨fun q => (hA.1 q).mul_left (hB.1 q), ?_⟩
    intro q r
    change A (B (R.factor q r)) = R.factor q r
    rw [hB.2, hA.2]
  inv_mem' := by
    intro A hA
    refine ⟨fun q => (hA.1 q).inv_left, ?_⟩
    intro q r
    apply A.injective
    change A (A.symm (R.factor q r)) = A (R.factor q r)
    rw [A.apply_symm_apply, hA.2]

end PolycyclicRecognition

end OAI

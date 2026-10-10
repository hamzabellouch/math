import OAI.Combinatorics.ContingencyTables.Transport.ChoiceContextEnumeration

namespace OAI

/-! # Balanced words are literal bounded physical transversal profiles -/

namespace ContingencyTables.SmallContextEnumeration

open scoped Classical
open SmallContextCoordinates SmallContextFibres SmallGraphProfiles

universe u

variable {I J : Type u}

lemma rawChoice_bounded (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (x : Cells small → Fin (U+1)) :
    ∀ a,rawChoice small U x a ≤ B a.1.val.1 a.1.val.2 :=
  naturalProfile_bounded (choiceProfile small B U hB x)

lemma rawChoice_balanced (small : I → J → Bool) (B : I → J → ℕ) (U : ℕ)
    (hB : ∀ i j,small i j=true → B i j=U) (x : Cells small → Fin (U+1)) :
    Balanced small B (rawChoice small U x) := choiceProfile_balanced small B U hB x

lemma rawChoice_injective (small : I → J → Bool) (U : ℕ) : Function.Injective (rawChoice small U) := by
  intro x y he
  funext a
  exact Fin.ext (congrFun he (a,false))

end ContingencyTables.SmallContextEnumeration

end OAI

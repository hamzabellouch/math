import Mathlib

namespace OAI

namespace OddKaplansky

@[irreducible] def sourceM : ℕ := Nat.choose 1200 600
@[irreducible] def sourcePrime : ℕ := Nat.minFac ((Nat.factorial sourceM)^2 + 1)

noncomputable section

def cellular {K G : Type} [Field K] [Group G]
    (d : MonoidAlgebra K G) (x : G → K) (g : G) : K :=
  d.coeff.sum fun u c => c * x (g * u)

def MainClaim : Prop :=
  sourcePrime.Prime ∧ Odd sourcePrime ∧
  ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K sourcePrime),
    Fintype.card K = sourcePrime^4 ∧
    ∃ (G : Type) (_ : Group G) (_ : Group.FG G),
      (∃ g : G, g ≠ 1 ∧ IsOfFinOrder g) ∧
      ∃ a b : MonoidAlgebra K G,
        a * b = 1 ∧ b * a ≠ 1 ∧
        Function.Injective (cellular b) ∧ ¬ Function.Surjective (cellular b)

theorem main_theorem : MainClaim := by
  sorry

end

end OddKaplansky

end OAI

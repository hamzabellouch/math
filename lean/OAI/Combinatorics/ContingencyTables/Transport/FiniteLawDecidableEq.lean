import OAI.Combinatorics.ContingencyTables.Transport.FinitePartialDraw

namespace OAI

/-! # Explicit decidable equality at finite-law application boundaries -/

namespace ContingencyTables.FirstSuccess

open ResidualMixture

universe u v

variable {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]

/-- The output equality decision only computes the same finite fibres;
it does not change the mapped probability law. Keeping the decisions
explicit avoids reducing a large concrete state type to match instances. -/
theorem mapLaw_decidableEq_irrel (d e : DecidableEq Y)
    (p : RationalLaw X) (f : X → Y) :
    @mapLaw X Y _ _ d p f=@mapLaw X Y _ _ e p f := by
  cases Subsingleton.elim d e
  rfl

theorem mapLaw_mass_decidableEq_irrel (d e : DecidableEq Y)
    (p : RationalLaw X) (f : X → Y) (y : Y) :
    (@mapLaw X Y _ _ d p f).mass y=(@mapLaw X Y _ _ e p f).mass y := by
  rw [mapLaw_decidableEq_irrel d e]

end ContingencyTables.FirstSuccess

namespace ContingencyTables.FairBits

open ResidualMixture FirstSuccess
open scoped Classical

universe u

variable {X : Type u} [Fintype X]

/-- The actual subset bit draw has its exact dyadic mass with any chosen
output equality decision. The draw and its embedding are unchanged. -/
theorem subsetBitDraw_mass_decidableEq (d : DecidableEq (Option X))
    (p : X → Prop) (k : ℕ) (h : Fintype.card {x // p x} ≤ 2^k) (x : X) :
    (@mapLaw (Fin k → Bool) (Option X) _ _ d
      (uniformLaw (α := Fin k → Bool)) (subsetBitDraw p k h)).mass (some x)=
        if p x then 1/(2:ℚ)^k else 0 := by
  let dX : DecidableEq X := Classical.decEq X
  have he := mapLaw_mass_decidableEq_irrel d (@Option.instDecidableEq X dX)
    (uniformLaw (α := Fin k → Bool)) (subsetBitDraw p k h) (some x)
  exact he.trans (@subsetBitDraw_mass X _ dX p k h x)

end ContingencyTables.FairBits

end OAI

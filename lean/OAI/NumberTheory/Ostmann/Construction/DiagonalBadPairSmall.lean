import OAI.NumberTheory.Ostmann.Construction.DiagonalBadPairQuadratic
import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexFinal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

theorem diagonalSmallTerm_nonneg (d : Decomposition) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (z : RemainingTerm sources seed V giant l) :
    0≤diagonalSmallTerm d sources seed V giant outside l p u z :=
  diagonalSmallMultiplier_nonneg _ _ _ _ _

theorem diagonalSmallTerm_reconstructCounterpart (d : Decomposition) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hsep : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current seed l))[i].origin))
    (v : AllowedFrequency V l)
    (x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (e : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Template.current seed l))))
    (he : CounterpartCompatible sources (Template.remainder (l+1) (Template.current seed l)) giant x e)
    (hx : (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass x≠0)
    (hy : (remainingPrior sources (Template.remainder (l+1) (Template.current seed l)) giant).mass
      (reconstructCounterpart sources (Template.remainder (l+1) (Template.current seed l)) giant x e he)≠0) :
    diagonalSmallTerm d sources seed V giant outside l p u
      (reconstructCounterpart sources (Template.remainder (l+1) (Template.current seed l)) giant x e he,v)=
    diagonalSmallTerm d sources seed V giant outside l p u (x,v) := by
  apply diagonalSmallTerm_eq_of_tag d sources seed V giant outside l p u
    (reconstructCounterpart sources (Template.remainder (l+1) (Template.current seed l)) giant x e he,v) (x,v) hy hx hsep
  exact congrArg (fun n : ℕ => (v.val,n))
    (reconstructCounterpart_product sources _ giant x e he)

theorem diagonal_bad_pair_quadratic_bound (d : Decomposition) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hsep : ∀i:Fin (Template.remainder (l+1) (Template.current seed l)).length,
      giant.DisjointMass (sources (Template.remainder (l+1) (Template.current seed l))[i].origin))
    (B : Equiv.Perm (RemainingIndex (Template.remainder (l+1) (Template.current seed l)))→Prop)
    (hB : ∀e,B e→B e.symm) (v : AllowedFrequency V l) :
    let T := Template.remainder (l+1) (Template.current seed l)
    let μ := remainingPrior sources T giant
    let A := fun x => diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (x,v)
    let F := fun x => diagonalSmallTerm d sources seed V giant outside l p u (x,v)
    (∑z : BadCounterpartPair sources T giant B,
      (μ.mass z.val.1*μ.mass (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1)*F z.val.1)*
        (A z.val.1*star (A (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1))).re)≤
    ∑z : BadCounterpartPair sources T giant B,
      (μ.mass z.val.1*μ.mass (reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1)*F z.val.1)*
        ‖A z.val.1‖^2 := by
  dsimp only
  apply badCounterpartPair_quadratic_bound sources _ giant B hB
    (fun x => diagonalSmallTerm d sources seed V giant outside l p u (x,v))
    (fun x => diagonalCoefficientTerm d sources seed V giant X G bins outside l p u (x,v))
  · intro x
    exact diagonalSmallTerm_nonneg d sources seed V giant outside l p u (x,v)
  · intro x e he hbe hx hy
    exact diagonalSmallTerm_reconstructCounterpart d sources seed V giant outside l p u hsep v x e he hx hy

end Ostmann.Construction

end

end OAI

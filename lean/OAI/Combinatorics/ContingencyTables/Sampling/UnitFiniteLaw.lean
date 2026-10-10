import OAI.Combinatorics.ContingencyTables.Sampling.UnitProfileSemantics
import OAI.Combinatorics.ContingencyTables.Sampling.AllSmallOuter

namespace OAI

/-! # The computed all-small walk has the proved uniform sampling law -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms FirstPaperPhysicalMarginal CompletionCounts
open FirstSuccess FairBits CompletionTranslation SmallContextCoordinates ResidualMixture
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
variable (e : Fin q ≃ Cells (paperSmall r c))
local notation "s" => smallProposalBits (I := Fin m) (J := Fin n)

attribute [local irreducible] FirstSuccess.mapLaw

private lemma mapped_walk_decidableEq_irrel {X Y : Type*} [Fintype X] [Fintype Y]
    (dX eX : DecidableEq X) (dY eY : DecidableEq Y)
    (K : X → RationalLaw X) (x : X) (n : ℕ) (f : X → Y) :
    @mapLaw X Y _ _ dY (@walkLaw X _ dX K x n) f=
      @mapLaw X Y _ _ eY (@walkLaw X _ eX K x n) f := by
  cases Subsingleton.elim dX eX
  cases Subsingleton.elim dY eY
  rfl

lemma unitCodeBitStep_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) :
    mapLaw (uniformLaw (α := Fin s → Bool)) (unitCodeBitStep r c e x)=unitSmallStep r c x := by
  have hp := decodedCodeProposal_law r c e htotal x
  calc
    _ = mapLaw (mapLaw (uniformLaw (α := Fin s → Bool)) (decodedCodeProposal r c e x))
        (fun z => z.getD x) := (mapLaw_comp _ _ _).symm
    _ = mapLaw (smallProposalLaw r c x) (fun z => z.getD x) :=
      congrArg (fun p : RationalLaw (Option (PaperStates r c)) => mapLaw p (fun z => z.getD x))
        hp
    _ = _ := by
      unfold unitSmallStep proposalStayLaw smallProposalLaw
      exact mapLaw_decidableEq_irrel _ _ _ _

def flatUnitCodeWalk (x : PaperStates r c) (n : ℕ) (bits : Fin (n*s) → Bool) : PaperStates r c :=
  wordWalk (unitCodeBitStep r c e) x n (GridBoundary.gridWordEquiv n s bits)

lemma flatUnitCodeWalk_law (htotal : (∑ i,r i)=∑ j,c j) (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (flatUnitCodeWalk r c e x n)=
      walkLaw (unitSmallStep r c) x n := by
  unfold flatUnitCodeWalk
  rw [←map_equiv (GridBoundary.gridWordEquiv n s),uniform_equiv]
  change wordWalkLaw _ _ _=_
  rw [wordWalkLaw_eq]
  exact congrArg (fun K => walkLaw K x n) (funext (unitCodeBitStep_law r c e htotal))

def unitCodeJointDraw (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n : ℕ) (bits : Fin (n*s) → Bool) : PaperStateJoint r c :=
  let z := flatUnitCodeWalk r c e x n bits
  ⟨z,fallback z⟩

lemma unitCodeJointDraw_law (htotal : (∑ i,r i)=∑ j,c j)
    (fallback : (z : PaperStates r c) → PaperFibre r c z) (x : PaperStates r c) (n : ℕ) :
    mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (unitCodeJointDraw r c e fallback x n)=
      mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (unitJointDraw r c fallback x n) := by
  calc
    _ = mapLaw (mapLaw (uniformLaw (α := Fin (n*s) → Bool)) (flatUnitCodeWalk r c e x n))
        (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c)) :=
      (mapLaw_comp _ (flatUnitCodeWalk r c e x n)
        (fun z => (⟨z,fallback z⟩ : PaperStateJoint r c))).symm
    _ = _ := by
      rw [flatUnitCodeWalk_law r c e htotal]
      exact (mapped_walk_decidableEq_irrel _ _ _ _ _ _ _ _).trans
        ((unitJointDraw_law r c fallback x n).symm.trans
          (mapLaw_decidableEq_irrel _ _ _ _))

def unitCodeOuterDraw (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n M : ℕ) (z₀ : Table r c)
    (bits : Fin (M*(n*s)) → Bool) : Table r c :=
  wordRetry (fun w => stateTrial r c (unitCodeJointDraw r c e fallback x n w)) z₀ M
    (GridBoundary.gridWordEquiv M (n*s) bits)

lemma unitCodeOuterDraw_law (htotal : (∑ i,r i)=∑ j,c j)
    (fallback : (z : PaperStates r c) → PaperFibre r c z)
    (x : PaperStates r c) (n M : ℕ) (z₀ : Table r c) :
    mapLaw (uniformLaw (α := Fin (M*(n*s)) → Bool))
      (unitCodeOuterDraw r c e fallback x n M z₀)=
      mapLaw (uniformLaw (α := Fin (M*(n*s)) → Bool))
        (unitOuterDraw r c fallback x n M z₀) := by
  unfold unitCodeOuterDraw
  rw [←map_equiv (GridBoundary.gridWordEquiv M (n*s)),uniform_equiv]
  change wordRetryLaw _ _ _=_
  rw [wordRetryLaw_eq,←retryLaw_map,unitCodeJointDraw_law r c e htotal,unitOuterDraw_law]
  exact congrArg (fun p : RationalLaw (PaperStateJoint r c) =>
    retryLaw p (stateTrial r c) z₀ M) (mapLaw_decidableEq_irrel _ _ _ _)

end
end ContingencyTables.SmallGraphProfiles

end OAI

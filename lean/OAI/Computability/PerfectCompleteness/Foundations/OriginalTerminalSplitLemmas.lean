import Mathlib.Logic.Equiv.Prod
import OAI.Computability.PerfectCompleteness.Foundations.TerminalCalls
import OAI.Computability.PerfectCompleteness.Sampling.SamplerCompositionLaws
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.OriginalTerminalSplit

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls SamplerComposition
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m k : Nat}

theorem expansionSpace_terminal (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (terminal : TerminalIndex repeats p),
      ExpansionSpace 𝕜 repeats p q A (drawIndex repeats p terminal) =
        RecursiveSampler.Tape 𝕜 repeats q (p.family A) := by
  induction p with
  | refl n => intro q A terminal; rfl
  | step i p ih =>
      intro q A terminal
      exact ih q (childFamily A i) terminal.2

theorem expansionSpace_exterior (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (j : DrawIndex repeats p), ¬ IsTerminal repeats p j →
      ExpansionSpace 𝕜 repeats p q A j = DrawSpace 𝕜 repeats p A j := by
  induction p with
  | refl n =>
      intro q A j hj
      exact False.elim (hj True.intro)
  | step i p ih =>
      intro q A j hj
      cases j with
      | inl j => rfl
      | inr j => exact ih q (childFamily A i) j.2 hj

variable (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u)

abbrev ExteriorIndex := {j : DrawIndex repeats p // ¬ IsTerminal repeats p j}

abbrev ExteriorTape := (j : ExteriorIndex repeats p) → DrawSpace 𝕜 repeats p A j.val

abbrev TerminalTape :=
  TerminalIndex repeats p → RecursiveSampler.Tape 𝕜 repeats q (p.family A)

def terminalFactorEquiv (terminal : TerminalIndex repeats p) :
    ExpansionSpace 𝕜 repeats p q A (drawIndex repeats p terminal) ≃
      RecursiveSampler.Tape 𝕜 repeats q (p.family A) :=
  Equiv.cast (expansionSpace_terminal 𝕜 repeats p q A terminal)

def exteriorFactorEquiv (j : ExteriorIndex repeats p) :
    ExpansionSpace 𝕜 repeats p q A j.val ≃ DrawSpace 𝕜 repeats p A j.val :=
  Equiv.cast (expansionSpace_exterior 𝕜 repeats p q A j.val j.property)

def terminalTapeEquiv :
    ((j : {j : DrawIndex repeats p // IsTerminal repeats p j}) →
      ExpansionSpace 𝕜 repeats p q A j.val) ≃ TerminalTape 𝕜 repeats p q A :=
  ((Equiv.piCongrLeft
    (fun j : {j : DrawIndex repeats p // IsTerminal repeats p j} =>
      ExpansionSpace 𝕜 repeats p q A j.val)
    (terminalSubtypeEquiv repeats p)).symm).trans
      (Equiv.piCongrRight (terminalFactorEquiv 𝕜 repeats p q A))

def splitExpanded : ExpandedTape 𝕜 repeats p q A ≃
    TerminalTape 𝕜 repeats p q A × ExteriorTape 𝕜 repeats p A :=
  (Equiv.piEquivPiSubtypeProd (IsTerminal repeats p)
    (ExpansionSpace 𝕜 repeats p q A)).trans
      (Equiv.prodCongr (terminalTapeEquiv 𝕜 repeats p q A)
        (Equiv.piCongrRight (exteriorFactorEquiv 𝕜 repeats p q A)))

def splitTape : RecursiveSampler.Tape 𝕜 repeats (p.append q) A ≃
    TerminalTape 𝕜 repeats p q A × ExteriorTape 𝕜 repeats p A :=
  (expandEquiv 𝕜 repeats p q A).trans (splitExpanded 𝕜 repeats p q A)

@[simp] theorem splitExpanded_terminal_apply
    (x : ExpandedTape 𝕜 repeats p q A) (terminal : TerminalIndex repeats p) :
    (splitExpanded 𝕜 repeats p q A x).1 terminal =
      terminalFactorEquiv 𝕜 repeats p q A terminal (x (drawIndex repeats p terminal)) := rfl

@[simp] theorem splitExpanded_exterior_apply
    (x : ExpandedTape 𝕜 repeats p q A) (j : ExteriorIndex repeats p) :
    (splitExpanded 𝕜 repeats p q A x).2 j =
      exteriorFactorEquiv 𝕜 repeats p q A j (x j.val) := rfl

variable [Finite 𝕜] [hA : ∀ s, Finite (A s)]

local instance familyFinite : ∀ s, Finite (p.family A s) :=
  fun s => hA (p.slotEmbedding s)

def terminalLaw : FiniteDistribution (TerminalTape 𝕜 repeats p q A) :=
  FiniteProduct.law (fun _ : TerminalIndex repeats p =>
    RecursiveSampler.tapeLaw 𝕜 repeats q (p.family A))

def exteriorLaw : FiniteDistribution (ExteriorTape 𝕜 repeats p A) :=
  FiniteProduct.law (fun j : ExteriorIndex repeats p =>
    FiniteDistribution.uniform (DrawSpace 𝕜 repeats p A j.val))

theorem terminalLaw_uniform :
    terminalLaw 𝕜 repeats p q A = FiniteDistribution.uniform (TerminalTape 𝕜 repeats p q A) := by
  simp only [terminalLaw, RecursiveSampler.tapeLaw_eq_uniform, UniformLinearImage.law_uniform]

theorem exteriorLaw_uniform :
    exteriorLaw 𝕜 repeats p A = FiniteDistribution.uniform (ExteriorTape 𝕜 repeats p A) :=
  UniformLinearImage.law_uniform

theorem split_tapeLaw :
    (RecursiveSampler.tapeLaw 𝕜 repeats (p.append q) A).pushforward
      (splitTape 𝕜 repeats p q A) =
        (terminalLaw 𝕜 repeats p q A).product (exteriorLaw 𝕜 repeats p A) := by
  rw [RecursiveSampler.tapeLaw_eq_uniform, FiniteDistribution.pushforward_equiv,
    terminalLaw_uniform, exteriorLaw_uniform]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card (RecursiveSampler.Tape 𝕜 repeats (p.append q) A) : ℝ) =
    (1 / (Fintype.card (TerminalTape 𝕜 repeats p q A) : ℝ)) *
      (1 / (Fintype.card (ExteriorTape 𝕜 repeats p A) : ℝ))
  rw [Fintype.card_congr (splitTape 𝕜 repeats p q A), Fintype.card_prod]
  simp only [Nat.cast_mul, one_div, mul_inv]

end
end PerfectCompleteness.OriginalTerminalSplit

end

section

namespace PerfectCompleteness.OriginalScalarReconstruction

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls SamplerComposition
open OriginalTerminalSplit
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m k : Nat}
variable (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u)

abbrev TerminalValues := TerminalIndex repeats p → space 𝕜 branch m (p.family A)

def terminalValueEquiv :
    ((j : {j : DrawIndex repeats p // IsTerminal repeats p j}) →
      DrawSpace 𝕜 repeats p A j.val) ≃ TerminalValues 𝕜 repeats p A :=
  ((Equiv.piCongrLeft
    (fun j : {j : DrawIndex repeats p // IsTerminal repeats p j} =>
      DrawSpace 𝕜 repeats p A j.val)
    (terminalSubtypeEquiv repeats p)).symm).trans
      (Equiv.piCongrRight (terminalSpaceEquiv 𝕜 repeats p A))

def prefixSplit : RecursiveSampler.Tape 𝕜 repeats p A ≃
    TerminalValues 𝕜 repeats p A × ExteriorTape 𝕜 repeats p A :=
  (Equiv.piEquivPiSubtypeProd (IsTerminal repeats p) (DrawSpace 𝕜 repeats p A)).trans
    (Equiv.prodCongr (terminalValueEquiv 𝕜 repeats p A) (Equiv.refl _))

def reconstruct (values : TerminalValues 𝕜 repeats p A)
    (exterior : ExteriorTape 𝕜 repeats p A) : space 𝕜 branch n A :=
  RecursiveSampler.evaluate 𝕜 repeats p A ((prefixSplit 𝕜 repeats p A).symm (values, exterior))

theorem collapseFactor_terminal :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (terminal : TerminalIndex repeats p)
      (x : ExpansionSpace 𝕜 repeats p q A (drawIndex repeats p terminal)),
      terminalSpaceEquiv 𝕜 repeats p A terminal
        (collapseFactor 𝕜 repeats p q A (drawIndex repeats p terminal) x) =
      RecursiveSampler.evaluate 𝕜 repeats q (p.family A)
        (terminalFactorEquiv 𝕜 repeats p q A terminal x) := by
  induction p with
  | refl n => intro q A terminal x; rfl
  | step i p ih =>
      intro q A terminal x
      exact ih q (childFamily A i) terminal.2 x

theorem collapseFactor_exterior :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (j : DrawIndex repeats p) (hj : ¬ IsTerminal repeats p j)
      (x : ExpansionSpace 𝕜 repeats p q A j),
      collapseFactor 𝕜 repeats p q A j x =
        exteriorFactorEquiv 𝕜 repeats p q A ⟨j, hj⟩ x := by
  induction p with
  | refl n =>
      intro q A j hj x
      exact False.elim (hj True.intro)
  | step i p ih =>
      intro q A j hj x
      cases j with
      | inl j => rfl
      | inr j => exact ih q (childFamily A i) j.2 hj x

theorem prefixSplit_collapseExpanded (q : Path branch m k)
    (x : ExpandedTape 𝕜 repeats p q A) :
    prefixSplit 𝕜 repeats p A (collapseExpanded 𝕜 repeats p q A x) =
      (fun terminal => RecursiveSampler.evaluate 𝕜 repeats q (p.family A)
        ((splitExpanded 𝕜 repeats p q A x).1 terminal),
        (splitExpanded 𝕜 repeats p q A x).2) := by
  apply Prod.ext
  · funext terminal
    exact collapseFactor_terminal 𝕜 repeats p q A terminal (x (drawIndex repeats p terminal))
  · funext j
    exact collapseFactor_exterior 𝕜 repeats p q A j.val j.property (x j.val)

theorem reconstruct_original (q : Path branch m k)
    (x : RecursiveSampler.Tape 𝕜 repeats (p.append q) A) :
    reconstruct 𝕜 repeats p A
      (fun terminal => RecursiveSampler.evaluate 𝕜 repeats q (p.family A)
        ((splitTape 𝕜 repeats p q A x).1 terminal))
      (splitTape 𝕜 repeats p q A x).2 =
        RecursiveSampler.evaluate 𝕜 repeats (p.append q) A x := by
  have hsplit := prefixSplit_collapseExpanded 𝕜 repeats p A q
    (expandEquiv 𝕜 repeats p q A x)
  change prefixSplit 𝕜 repeats p A (collapseSuffix 𝕜 repeats p q A x) =
    (fun terminal => RecursiveSampler.evaluate 𝕜 repeats q (p.family A)
      ((splitTape 𝕜 repeats p q A x).1 terminal),
      (splitTape 𝕜 repeats p q A x).2) at hsplit
  unfold reconstruct
  rw [← hsplit, Equiv.symm_apply_apply]
  exact evaluate_collapseSuffix 𝕜 repeats p q A x

end
end PerfectCompleteness.OriginalScalarReconstruction

end

end OAI

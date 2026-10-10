import Mathlib.Logic.Equiv.Prod
import OAI.Computability.PerfectCompleteness.Construction.HiddenBucketBias
import OAI.Computability.PerfectCompleteness.Foundations.TerminalCalls
import OAI.Computability.PerfectCompleteness.Sampling.CutSamplerRefinement
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.CutTerminalSplit

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

theorem refinedSpace_eq_terminal (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u) (terminal : TerminalIndex repeats p),
      CutSamplerRefinement.RefinedSpace 𝕜 repeats p A (drawIndex repeats p terminal) =
        CutSamplerRefinement.RefinedSpace 𝕜 repeats (.refl m) (p.family A) () := by
  induction p with
  | refl n =>
      intro A terminal
      cases terminal
      rfl
  | step i p ih =>
      intro A terminal
      exact ih (childFamily A i) terminal.2

variable (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
  (p : Path branch n (m + 1)) (A : Slots branch n → Type u)

abbrev TerminalFactor :=
  (i : Fin (branch m)) → squareSpace (space 𝕜 branch m (childFamily (p.family A) i))

abbrev TerminalTape := TerminalIndex repeats p → TerminalFactor 𝕜 p A

abbrev ExteriorIndex := {j : DrawIndex repeats p // ¬ IsTerminal repeats p j}

abbrev ExteriorTape :=
  (j : ExteriorIndex repeats p) → CutSamplerRefinement.RefinedSpace 𝕜 repeats p A j.val

def terminalFactorEquiv (terminal : TerminalIndex repeats p) :
    CutSamplerRefinement.RefinedSpace 𝕜 repeats p A (drawIndex repeats p terminal) ≃
      TerminalFactor 𝕜 p A :=
  Equiv.cast (refinedSpace_eq_terminal 𝕜 repeats p A terminal)

def terminalTapeEquiv :
    ((j : {j : DrawIndex repeats p // IsTerminal repeats p j}) →
      CutSamplerRefinement.RefinedSpace 𝕜 repeats p A j.val) ≃
        TerminalTape 𝕜 repeats p A :=
  ((Equiv.piCongrLeft
    (fun j : {j : DrawIndex repeats p // IsTerminal repeats p j} =>
      CutSamplerRefinement.RefinedSpace 𝕜 repeats p A j.val)
    (terminalSubtypeEquiv repeats p)).symm).trans
      (Equiv.piCongrRight (terminalFactorEquiv 𝕜 repeats p A))

def splitTape :
    CutSamplerRefinement.Tape 𝕜 repeats p A ≃
      TerminalTape 𝕜 repeats p A × ExteriorTape 𝕜 repeats p A :=
  (Equiv.piEquivPiSubtypeProd (IsTerminal repeats p)
    (CutSamplerRefinement.RefinedSpace 𝕜 repeats p A)).trans
      (Equiv.prodCongr (terminalTapeEquiv 𝕜 repeats p A) (Equiv.refl _))

@[simp] theorem splitTape_terminal_apply
    (x : CutSamplerRefinement.Tape 𝕜 repeats p A) (terminal : TerminalIndex repeats p) :
    (splitTape 𝕜 repeats p A x).1 terminal =
      terminalFactorEquiv 𝕜 repeats p A terminal (x (drawIndex repeats p terminal)) := rfl

@[simp] theorem splitTape_exterior_apply
    (x : CutSamplerRefinement.Tape 𝕜 repeats p A) (j : ExteriorIndex repeats p) :
    (splitTape 𝕜 repeats p A x).2 j = x j.val := rfl

variable [Finite 𝕜] [∀ s, Finite (A s)]

instance childSquareFintype (i : Fin (branch m)) :
    Fintype (squareSpace (space 𝕜 branch m (childFamily (p.family A) i))) :=
  Fintype.ofFinite _

def terminalLaw : FiniteDistribution (TerminalTape 𝕜 repeats p A) :=
  FiniteProduct.law (fun _ : TerminalIndex repeats p =>
    FiniteProduct.law (fun i : Fin (branch m) =>
      FiniteDistribution.uniform
        (squareSpace (space 𝕜 branch m (childFamily (p.family A) i)))))

def exteriorLaw : FiniteDistribution (ExteriorTape 𝕜 repeats p A) :=
  FiniteProduct.law (fun j : ExteriorIndex repeats p =>
    FiniteDistribution.uniform (CutSamplerRefinement.RefinedSpace 𝕜 repeats p A j.val))

theorem terminalLaw_uniform :
    terminalLaw 𝕜 repeats p A = FiniteDistribution.uniform (TerminalTape 𝕜 repeats p A) := by
  simp only [terminalLaw, UniformLinearImage.law_uniform]

theorem exteriorLaw_uniform :
    exteriorLaw 𝕜 repeats p A = FiniteDistribution.uniform (ExteriorTape 𝕜 repeats p A) :=
  UniformLinearImage.law_uniform

theorem split_tapeLaw :
    (CutSamplerRefinement.tapeLaw 𝕜 repeats p A).pushforward (splitTape 𝕜 repeats p A) =
      (terminalLaw 𝕜 repeats p A).product (exteriorLaw 𝕜 repeats p A) := by
  unfold CutSamplerRefinement.tapeLaw
  rw [UniformLinearImage.law_uniform, FiniteDistribution.pushforward_equiv,
    terminalLaw_uniform, exteriorLaw_uniform]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card (CutSamplerRefinement.Tape 𝕜 repeats p A) : ℝ) =
    (1 / (Fintype.card (TerminalTape 𝕜 repeats p A) : ℝ)) *
      (1 / (Fintype.card (ExteriorTape 𝕜 repeats p A) : ℝ))
  rw [Fintype.card_congr (splitTape 𝕜 repeats p A), Fintype.card_prod]
  simp only [Nat.cast_mul, one_div, mul_inv]

theorem terminal_marginal :
    (CutSamplerRefinement.tapeLaw 𝕜 repeats p A).pushforward
        (fun x => (splitTape 𝕜 repeats p A x).1) = terminalLaw 𝕜 repeats p A := by
  rw [← FiniteDistribution.pushforward_comp (CutSamplerRefinement.tapeLaw 𝕜 repeats p A)
    (splitTape 𝕜 repeats p A) Prod.fst, split_tapeLaw]
  exact HiddenBucketBias.product_fst
    (terminalLaw 𝕜 repeats p A) (exteriorLaw 𝕜 repeats p A)

theorem terminal_marginal_uniform :
    (CutSamplerRefinement.tapeLaw 𝕜 repeats p A).pushforward
        (fun x => (splitTape 𝕜 repeats p A x).1) =
      FiniteDistribution.uniform (TerminalTape 𝕜 repeats p A) := by
  rw [terminal_marginal, terminalLaw_uniform]

end
end PerfectCompleteness.CutTerminalSplit

end

end OAI

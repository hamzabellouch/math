import Mathlib
import OAI.Computability.MaxCut.Games.FinishBounds
import OAI.Computability.MaxCut.Machines.MachineSubdivisionCorrespondence
import OAI.Computability.MaxCut.Machines.MachineProductLoop
import OAI.Computability.MaxCut.PCP.KernelIteration

namespace OAI

section

/-!
The final graph product inherits the alphabet-independent repetition estimate
through its proved uniform occurrence law and arbitrary-local-strategy bridge.
The only input soundness premise is the base graph's actual finite maximum.
-/

namespace MaxCutGames.Explicit.BipartiteGame

open MaxCutGames.Foundations.Games

noncomputable section

variable {L R E A : Type*}
  [Fintype L] [Fintype R] [Fintype E] [Fintype A]
  [Nonempty E] [Nonempty A]

theorem product_soundness_rate (G : BipartiteGame L R E A) (t : ℕ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.product t).toGame.value ≤ (1 - (1 : ℝ) / 10240000) ^ t := by
  rw [product_value_eq_repetition]
  exact MaxCutGames.Repetition.final_repetition_value
    G.toGame G.toGame_isProjection t hvalue

theorem product_soundness (G : BipartiteGame L R E A) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.product t).toGame.value ≤ δ :=
  (G.product_soundness_rate t hvalue).trans hcount

theorem product_explicit_soundness [DecidableEq A]
    (G : BipartiteGame L R E A) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.value ≤ 1 - (1 : ℝ) / 800) :
    (G.product t).value ≤ δ := by
  classical
  rw [← toGame_value]
  exact G.product_soundness t hcount (by simpa only [toGame_value] using hvalue)

end

noncomputable section

variable {L R E : Type*} [Fintype L] [Fintype R] [Fintype E] [Nonempty E]

theorem binaryProduct_soundness_rate {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.binaryProduct t).toGame.value ≤ (1 - (1 : ℝ) / 10240000) ^ t := by
  rw [binaryProduct_value_eq_repetition]
  exact MaxCutGames.Repetition.final_repetition_value
    G.toGame G.toGame_isProjection t hvalue

theorem binaryProduct_soundness {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.toGame.value ≤ 1 - (1 : ℝ) / 800) :
    (G.binaryProduct t).toGame.value ≤ δ :=
  (G.binaryProduct_soundness_rate t hvalue).trans hcount

theorem binaryProduct_explicit_soundness {ell : ℕ}
    (G : BipartiteGame L R E (Fin ell → ZMod 2)) (t : ℕ) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : G.value ≤ 1 - (1 : ℝ) / 800) :
    (G.binaryProduct t).value ≤ δ := by
  rw [← toGame_value]
  exact G.binaryProduct_soundness t hcount (by simpa only [toGame_value] using hvalue)

end

end MaxCutGames.Explicit.BipartiteGame

namespace MaxCutGames.Explicit.ProductPaddedOutput

open MaxCutGames.Foundations
open Target
open MachineOutputContract

noncomputable section

variable {q : ℕ} [Nonempty (Fin q)]

/-- Soundness for the actual globally numbered, fully tabulated output. -/
theorem output_soundness_rate (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤
      (1 - (1 : ℝ) / 10240000) ^ t := by
  let : Nonempty (Fin H.constraints.length) := ⟨⟨0, H.constraintCount_positive⟩⟩
  rw [output_value_eq_repetition]
  apply MaxCutGames.Repetition.final_repetition_value
    presentation.toBipartiteGame.toGame presentation.toBipartiteGame.toGame_isProjection
  simpa only [BipartiteGame.toGame_value, presentation.toBipartiteGame_value] using hvalue

theorem output_soundness (H : Instance q) (presentation : SimpleBipartite H)
    (t : ℕ) (ht : 0 < t) {δ : ℝ}
    (hcount : (1 - (1 : ℝ) / 10240000) ^ t ≤ δ)
    (hvalue : Integration.InstanceValue.value H ≤ 1 - (1 : ℝ) / 800) :
    Integration.InstanceValue.value (output H presentation t ht) ≤ δ :=
  (output_soundness_rate H presentation t ht hvalue).trans hcount

end
end MaxCutGames.Explicit.ProductPaddedOutput
end

/-!
The concrete final composition, once the matrix reduction has been proved.
This constructor copies the actual occurrence list, subdivides every occurrence
into four edges, and runs the full tuple-product machine. Its hypotheses are
the matrix reduction's actual value bounds and finite-machine computation.
It is an intermediate composition theorem, not the unconditional v2 endpoint.
-/

namespace MaxCutGames.FinishReduction

open MaxCutGames.Foundations Target
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Integration
open Explicit

noncomputable section

/-- Compose the proved matrix reduction with the explicit three-stage finish.
All parameters, machines, alphabets, and time polynomials precede the input.
The original raw binary input codec is retained by sequential composition. -/
def of_matrix_reduction {ε δ : ℝ} (P : ParameterSelection.OuterParameters ε δ)
    {q s : ℕ} (hq : 2 ≤ q) (hs : 1 ≤ s)
    (coordinates : Fin q ≃ BinaryLinear.Vector s)
    (matrix : List Bool → Instance q)
    (translations : ∀ input, TranslationTarget.IsTranslationInstance coordinates (matrix input))
    (computation : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
      gameBits matrix)
    (finiteAlphabet : MachineFiniteAlphabet.FiniteAlphabet computation.tm)
    (d : ℚ) (hd : d ≤ P.epsilon0 / P.repetitions)
    (complete : ∀ input, BinaryLanguage.language input →
      1 - (d : ℝ) ≤ InstanceValue.value (matrix input))
    (sound : ∀ input, ¬BinaryLanguage.language input →
      InstanceValue.value (matrix input) ≤ 99 / 100) :
    MachineOutputContract.BinaryGapReduction ε δ := by
  classical
  have hqpos : 0 < q := by omega
  have hC : 0 < P.copies := by have h := P.copies_large; omega
  letI : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  let rounded := fun input => UniformTarget.construct P.copies hC (matrix input)
  have roundedTranslations : ∀ input,
      TranslationTarget.IsTranslationInstance coordinates (rounded input) := fun input =>
    UniformTarget.translations P.copies hC (matrix input) coordinates (translations input)
  let roundedMachine := MachineSequential.composeBits
    (f := matrix) (g := UniformTarget.construct P.copies hC) computation
    (MachineUniformRun.computation (q := q) P.copies hC)
  have roundedFinite : MachineFiniteAlphabet.FiniteAlphabet roundedMachine.tm :=
    MachineFiniteAlphabet.composeBits
      (f := matrix) (g := UniformTarget.construct P.copies hC) computation
      (MachineUniformRun.computation (q := q) P.copies hC) finiteAlphabet
      (MachineUniformRun.finiteAlphabet (q := q) P.copies hC)
  let base := fun input => SubdivisionTarget.subdivide (rounded input)
  let basePresentation := fun input => SubdivisionTarget.simpleBipartite (rounded input)
  let baseMachine := MachineSubdivisionCompose.translationComputableInPolyTime
    coordinates roundedMachine roundedTranslations
  have baseFinite : MachineFiniteAlphabet.FiniteAlphabet baseMachine.tm :=
    MachineSubdivisionCompose.finiteAlphabet roundedMachine
      (fun input => MachineSubdivisionCorrespondence.translations_involutive
        coordinates (rounded input) (roundedTranslations input)) roundedFinite
  let output := fun input => ProductPaddedOutput.output (base input)
    (basePresentation input) P.repetitions P.repetitions_pos
  let outputMachine := MachineProductRuntime.compose baseMachine basePresentation
    P.repetitions P.repetitions_pos
  have hqout : 2 ≤ q ^ P.repetitions :=
    hq.trans (Nat.le_self_pow P.repetitions_pos.ne' q)
  have hqoutpos : 0 < q ^ P.repetitions := by omega
  have baseValue (input : List Bool) :
      InstanceValue.value (base input) =
        1 - (1 - InstanceValue.value (matrix input)) / 4 := by
    dsimp [base, rounded]
    rw [SubdivisionTarget.value_eq _ hqpos,
      UniformTarget.value P.copies hC (matrix input) hqpos]
  have hτ : (0 : ℝ) < (P.pStar : ℝ) := by exact_mod_cast P.pStar_pos
  have hτsmall : (P.pStar : ℝ) ≤ 1 / 200 := by
    simpa only [ParameterSelection.OuterParameters.pStar, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_one]
      using ((Rat.cast_le (K := ℝ)).mpr P.reciprocal_small)
  have hτbudget : (P.pStar : ℝ) ≤ (P.epsilon0 : ℝ) / P.repetitions := by
    exact_mod_cast P.reciprocal_budget
  have hdbudget : (d : ℝ) ≤ (P.epsilon0 : ℝ) / P.repetitions := by
    exact_mod_cast hd
  have hε0 : (0 : ℝ) ≤ (P.epsilon0 : ℝ) := by
    exact_mod_cast P.epsilon0_pos.le
  have roundingError (input : List Bool) :
      |InstanceValue.value (base input) -
        (1 - (1 - InstanceValue.value (matrix input)) / 4)| ≤ (P.pStar : ℝ) / 4 := by
    rw [baseValue input, sub_self, abs_zero]
    positivity
  refine {
    alphabet := q ^ P.repetitions
    alphabetAtLeastTwo := hqout
    dimension := s * P.repetitions
    dimensionPositive := by
      have hpos := Nat.mul_pos (show 0 < s by omega) P.repetitions_pos
      omega
    coordinates := ProductPaddedOutput.finalCoordinates coordinates P.repetitions
    construct := output
    simpleBipartite := fun input => ProductPaddedOutput.simpleBipartite
      (base input) (basePresentation input) P.repetitions P.repetitions_pos
    translations := fun input => ProductPaddedOutput.output_translations
      (base input) (basePresentation input) coordinates
      (SubdivisionTarget.subdivide_translation coordinates (rounded input)
        (roundedTranslations input)) P.repetitions P.repetitions_pos
    computation := outputMachine
    finiteAlphabet := MachineProductRuntime.compose_finiteAlphabet
      baseMachine basePresentation P.repetitions P.repetitions_pos baseFinite
    completeness := ?_
    soundness := ?_
  }
  · intro input yes
    apply (InstanceValue.exists_rate_ge_iff (output input) hqoutpos (1 - ε)).mpr
    have hbase := FinishBounds.subdivision_completeness _ _ (d : ℝ) (P.pStar : ℝ)
      (complete input yes) (roundingError input)
    have hproduct := ProductPaddedOutput.output_completeness (base input)
      (basePresentation input) P.repetitions P.repetitions_pos
      (error := 1 - InstanceValue.value (base input)) (by linarith)
    exact FinishBounds.final_completeness _ _ (d : ℝ) (P.pStar : ℝ)
      (P.epsilon0 : ℝ) ε P.repetitions P.repetitions_pos hbase hproduct
      hdbudget hτbudget hε0 P.epsilon0_le
  · intro input no
    apply (InstanceValue.forall_rate_le_iff (output input) hqoutpos δ).mpr
    have hbase := FinishBounds.subdivision_soundness _ _ (P.pStar : ℝ)
      (sound input no) hτsmall (roundingError input)
    exact (ProductPaddedOutput.output_soundness (base input) (basePresentation input)
      P.repetitions P.repetitions_pos P.soundness_rate hbase).trans P.delta0_le

end
end MaxCutGames.FinishReduction

end OAI

import OAI.Computability.PerfectCompleteness.Construction.FlexibleLocalCompletionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.LegalOutputLemmas
import OAI.Computability.PerfectCompleteness.Machines.CanonicalLabelEncoding
import OAI.Computability.PerfectCompleteness.Machines.LocalCompletionMachineLemmas

namespace OAI

section

namespace PerfectCompleteness.CanonicalLocalCompletion

open scoped Classical
open Turing UniqueGamesTheorem.Foundations.Complexity UniqueGamesTheorem.Foundations.Games
open SourceClause CanonicalKeys CanonicalGame CanonicalKeyEncoding CanonicalLabelEncoding
open CompletionSoundness CompletionSoundness.LegalProjectionGame

noncomputable section

def alphabet (n : Nat) (δ : ℚ) : Nat := CompletionAlphabet.size (partitionWidth n) δ

theorem alphabet_positive (n : Nat) (δ : ℚ) : 0 < alphabet n δ :=
  CompletionAlphabet.size_positive (partitionWidth n) δ

theorem partitionWidth_le_alphabet (n : Nat) (δ : ℚ) : partitionWidth n ≤ alphabet n δ :=
  CompletionAlphabet.cap_le_size (partitionWidth n) δ

theorem partitionWidth_le_leftAlphabet (n : Nat) (δ : ℚ) :
    partitionWidth n ≤ 2 * alphabet n δ := by
  have h := partitionWidth_le_alphabet n δ
  omega

theorem alphabet_ge_two (n : Nat) (δ : ℚ) : 2 ≤ alphabet n δ := by
  have hpos : 0 < partitionWidth n := by
    rw [partitionWidth_eq]
    exact pow_pos (by decide) _
  have hcap : partitionWidth n + 1 ≤ alphabet n δ := le_max_left _ _
  omega

local instance rightAlphabet_nonempty (n : Nat) (δ : ℚ) : Nonempty (Fin (alphabet n δ)) :=
  ⟨⟨0, alphabet_positive n δ⟩⟩

local instance leftAlphabet_nonempty (n : Nat) (δ : ℚ) : Nonempty (Fin (2 * alphabet n δ)) :=
  ⟨⟨0, Nat.mul_pos (by decide) (alphabet_positive n δ)⟩⟩

variable {v m n : Nat} {E I B : Type*} {V : I → Type*}
  [DecidableEq I] [∀ i, AddCommGroup (V i)]
  [∀ i, Module DirectionQuotient.F2 (V i)]
  [Finite I] [∀ i, Finite (V i)] [Finite B]
  {clauses : Fin m → NormalizedClause v}
  (F : BlockFamily clauses n E I V B)

def legalL (δ : ℚ) (x : LeftVertex F) : LeftLabel F x ↪ Fin (2 * alphabet n δ) :=
  labelEmbedding x.val (partitionWidth_le_leftAlphabet n δ)

def legalR (δ : ℚ) (y : RightVertex F) : RightLabel F y ↪ Fin (alphabet n δ) :=
  labelEmbedding y.val (partitionWidth_le_alphabet n δ)

omit [DecidableEq I] [Finite I] [∀ index, Finite (V index)] [Finite B] in
@[simp] theorem legalL_val (δ : ℚ) (x : LeftVertex F) (label : LeftLabel F x) :
    (legalL F δ x label).val = (partEnum n label.val).val := rfl

omit [Finite I] [∀ index, Finite (V index)] [Finite B] in
@[simp] theorem legalR_val (δ : ℚ) (y : RightVertex F) (label : RightLabel F y) :
    (legalR F δ y label).val = (partEnum n label.val).val := rfl

def defaultL (x : LeftVertex F) : LeftLabel F x := Classical.choice inferInstance

variable [Fintype E] [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ x, Fintype (LeftLabel F x)] [∀ y, Fintype (RightLabel F y)]

omit [DecidableEq I] [Finite I] [∀ index, Finite (V index)] [Finite B] [Fintype E]
  [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem leftLabel_card_le (δ : ℚ) (x : LeftVertex F) :
    Fintype.card (LeftLabel F x) ≤ alphabet n δ := by
  let : Fintype (KeyLabel x.val) := inferInstanceAs (Fintype (LeftLabel F x))
  exact (label_card_le x.val).trans (partitionWidth_le_alphabet n δ)

omit [Finite I] [∀ index, Finite (V index)] [Finite B] [Fintype E]
  [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (LeftLabel F vertex)] in
theorem rightLabel_card_le (δ : ℚ) (y : RightVertex F) :
    Fintype.card (RightLabel F y) ≤ alphabet n δ := by
  let : Fintype (KeyLabel y.val) := inferInstanceAs (Fintype (RightLabel F y))
  exact (label_card_le y.val).trans (partitionWidth_le_alphabet n δ)

omit [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem small (μ : FiniteDistribution E) :
    ∀ e b, Fintype.card
      {a : LeftLabel F ((game F μ).left e) // (game F μ).projection e a = b} ≤ 2 := by
  intro e b
  rw [Fintype.card_eq_nat_card]
  change Nat.card {a : LeftLabel F (leftAt F e) // edge F e a = b} ≤ 2
  exact edge_at_most_two F e b

def input (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    LocalCompletionFamily.Input (alphabet n δ) :=
  LocalCompletionGame.input (game F μ) (legalL F δ) (legalR F δ) (defaultL F) e

omit [Finite I] [∀ index, Finite (V index)] [Finite B]
  [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem input_mask (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    (input F μ δ e).1 = paddedMask (leftKey F e) := by
  funext a
  apply Bool.eq_iff_iff.mpr
  exact (LocalCompletionGame.input_mask_true
    (game F μ) (legalL F δ) (legalR F δ) (defaultL F) e a).trans
    (paddedMask_eq_true_iff (leftKey F e) (partitionWidth_le_leftAlphabet n δ) a).symm

omit [Finite I] [∀ index, Finite (V index)] [Finite B]
  [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem input_image_legal (μ : FiniteDistribution E) (δ : ℚ) (e : E)
    (label : LeftLabel F (leftAt F e)) :
    (input F μ δ e).2 (legalL F δ (leftAt F e) label) =
      legalR F δ (rightAt F e) (edge F e label) :=
  LocalCompletionGame.input_image_legal
    (game F μ) (legalL F δ) (legalR F δ) (defaultL F) e label

omit [Finite I] [∀ index, Finite (V index)] [Finite B]
  [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem input_independent_of_law (μ ν : FiniteDistribution E) (δ : ℚ) (e : E) :
    input F μ δ e = input F ν δ e := rfl

omit [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem input_admissible (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    LocalCompletionFamily.Admissible (input F μ δ e) :=
  LocalCompletionGame.input_admissible
    (game F μ) (legalL F δ) (legalR F δ) (defaultL F) (by
      intro occurrence label
      rw [Fintype.card_eq_nat_card]
      have h := small F μ occurrence label
      rw [Fintype.card_eq_nat_card] at h
      exact h) e

def result (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    LocalCompletionFamily.Result (alphabet n δ) :=
  LocalCompletionFamily.lookup (alphabet_positive n δ) (input F μ δ e)

omit [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem result_correct (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    LocalCompletionFamily.Correct (input F μ δ e) (result F μ δ e) :=
  LocalCompletionFamily.lookup_correct (alphabet_positive n δ) _ (input_admissible F μ δ e)

def family (μ : FiniteDistribution E) (δ : ℚ) :
    (game F μ).CompletionFamily (legalL F δ) (legalR F δ) :=
  LocalCompletionGame.family (game F μ) (legalL F δ) (legalR F δ) (defaultL F)
    (alphabet_positive n δ) (by
      intro occurrence label
      rw [Fintype.card_eq_nat_card]
      have h := small F μ occurrence label
      rw [Fintype.card_eq_nat_card] at h
      exact h)

omit [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
@[simp] theorem family_size (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    (family F μ δ).size e = LocalCompletionFamily.activeCount (result F μ δ e) := rfl

omit [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
@[simp] theorem family_map (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    (family F μ δ).map e = LocalCompletionFamily.table (result F μ δ e) := rfl

omit [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem family_size_le (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    (family F μ δ).size e ≤ 2 * alphabet n δ :=
  LocalCompletionFamily.activeCount_le (result F μ δ e)

def machine_output (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    TM2OutputsInTime
      (LocalCompletionSerialization.computation (alphabet_positive n δ)).tm
      (LocalCompletionMachine.inputBits (input F μ δ e))
      (some (LocalCompletionSerialization.payloadBits (result F μ δ e))) 1 :=
  LocalCompletionSerialization.machine_output (alphabet_positive n δ) (input F μ δ e)

omit [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem payload_parses (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    decodeWords (LocalCompletionSerialization.payloadBits (result F μ δ e)) >>=
        LocalCompletionSerialization.parsePayload (alphabet n δ) =
      some ((List.finRange (LocalCompletionFamily.activeCount (result F μ δ e))).map
        (LocalCompletionSerialization.projection (result_correct F μ δ e))) := by
  rw [LocalCompletionSerialization.decode_payloadBits]
  exact LocalCompletionSerialization.parse_payload (result_correct F μ δ e)

omit [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem parsed_projection_eq_family_map (μ : FiniteDistribution E) (δ : ℚ) (e : E)
    (seed : Fin ((family F μ δ).size e)) (a : Fin (2 * alphabet n δ)) :
    (LocalCompletionSerialization.projection (result_correct F μ δ e) seed).images[a] =
      (family F μ δ).map e seed a :=
  LocalCompletionSerialization.projection_apply (result_correct F μ δ e) seed a

omit [Finite I] [∀ index, Finite (V index)] [Finite B]
  [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ vertex, Fintype (RightLabel F vertex)] in
theorem payload_length_le (μ : FiniteDistribution E) (δ : ℚ) (e : E) :
    (LocalCompletionSerialization.payloadBits (result F μ δ e)).length ≤
      (1 + (2 * alphabet n δ) * (2 * alphabet n δ)) * (2 * alphabet n δ + 1) :=
  LocalCompletionSerialization.payloadBits_length_le _

theorem family_value_le (μ : FiniteDistribution E) (δ : ℚ) (hδ : 0 < δ) :
    (family F μ δ).game.value ≤ (game F μ).value + (δ : ℝ) / 3 := by
  apply (family F μ δ).value_le_of_bound ((δ : ℝ) / 3)
  intro e
  have hδreal : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have h := CompletionParameters.residual_le_third (alphabet_positive n δ)
    (leftLabel_card_le F δ (leftAt F e)) hδreal
    (CompletionAlphabet.size_budget (partitionWidth n) δ hδ)
  simp only [Fintype.card_fin]
  rw [Fintype.card_eq_nat_card]
  rw [Fintype.card_eq_nat_card] at h
  simpa only [CanonicalGame.game] using h

theorem family_value_of_satisfying (μ : FiniteDistribution E) (δ : ℚ)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (family F μ δ).game.value = 1 := by
  let : Nonempty E := by
    by_contra hempty
    have : IsEmpty E := ⟨fun e => hempty ⟨e⟩⟩
    have hnormalized := μ.normalized
    simp at hnormalized
  apply (family F μ δ).value_eq_one
  exact CanonicalOutput.game_value_of_satisfying F μ assignment hsat

end
end PerfectCompleteness.CanonicalLocalCompletion

end

end OAI

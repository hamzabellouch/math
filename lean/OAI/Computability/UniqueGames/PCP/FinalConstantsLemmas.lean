import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.Computability.UniqueGames.PCP.AlphabetGraphLemmas
import OAI.Computability.UniqueGames.PCP.PoweringOpinionsLemmas
import OAI.Computability.UniqueGames.PCP.PoweringTableSemanticsLemmas
import OAI.Computability.UniqueGames.PCP.Preprocessing

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalConstants

def alphabet : Nat := 64
def compositionLoss : Nat := 12288
def denominator : Nat := 16 * alphabet ^ 4 * 66 * compositionLoss
def windowHalf : Nat := denominator * Preprocessing.sizeFactor
def windowSize : Nat := 2 * windowHalf + 1
def smoothingScale : Nat := 4 * alphabet * windowHalf
def endpointLength : Nat := smoothingScale ^ 2
def walkLength : Nat := 2 * endpointLength + 1

noncomputable def gain : ℝ := (windowSize : ℝ) / denominator
noncomputable def cap : ℝ := 1 / (walkLength : ℝ)

theorem denominator_positive : 0 < denominator := by
  norm_num [denominator, alphabet, compositionLoss]

theorem windowHalf_positive : 0 < windowHalf :=
  Nat.mul_pos denominator_positive Preprocessing.sizeFactor_positive

theorem walkLength_positive : 0 < walkLength := by
  simp [walkLength]

theorem gain_large : 2 * (Preprocessing.sizeFactor : ℝ) ≤ gain := by
  have hd : (0 : ℝ) < denominator := by exact_mod_cast denominator_positive
  apply (le_div_iff₀ hd).2
  simp only [windowSize, windowHalf, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat]
  nlinarith

theorem cap_positive : 0 < cap := by
  exact one_div_pos.mpr (by exact_mod_cast walkLength_positive)

theorem cap_le_one : cap ≤ 1 := by
  apply (div_le_one (by exact_mod_cast walkLength_positive)).2
  exact_mod_cast walkLength_positive

/-- The exact fixed constants make a whole round double the input gap until
the fixed positive threshold `cap` is reached. -/
theorem composed_gap (epsilon : ℝ) (he : 0 ≤ epsilon) :
    min (2 * epsilon) cap ≤
      gain * min (epsilon / (Preprocessing.sizeFactor : ℝ))
        (1 / (walkLength : ℝ)) := by
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hs1 : (1 : ℝ) ≤ Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have hg : 0 ≤ gain := le_trans (by positivity) gain_large
  rw [mul_min_of_nonneg _ _ hg]
  apply min_le_min
  · calc
      2 * epsilon = (2 * (Preprocessing.sizeFactor : ℝ)) *
          (epsilon / (Preprocessing.sizeFactor : ℝ)) := by field_simp
      _ ≤ gain * (epsilon / (Preprocessing.sizeFactor : ℝ)) :=
        mul_le_mul_of_nonneg_right gain_large (div_nonneg he hs.le)
  · change cap ≤ gain * cap
    have hgain : 1 ≤ gain := by linarith [gain_large]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hgain cap_positive.le

end UniqueGamesTheorem.Foundations.PCP.FinalConstants

end

section

/-!
The actual fixed-parameter graph transformation in one PCP amplification round.
It preprocesses the input graph, checks all edges of each bounded walk using
local endpoint labels, and applies the checked constant-query alphabet reduction.
The bounded address list is explicit fixed data shared by every input graph.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.PCP.AmplificationRound

abbrev Label := QueryIncidence.Label 6
abbrev Addresses := PoweringLabels.PortWords Preprocessing.Port FinalConstants.walkLength
abbrev PoweredAlphabet :=
  PoweringLabels.PaddedLabel Preprocessing.Port FinalConstants.walkLength Label

instance : Fintype PoweredAlphabet := Fintype.ofFinite _
instance : DecidableEq PoweredAlphabet := Classical.decEq _

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

abbrev PoweredDart (G : ConstraintGraph V E Label) :=
  PoweringTest.Dart (Preprocessing.Vertex G) Preprocessing.Port
    (2 * FinalConstants.endpointLength)

instance (G : ConstraintGraph V E Label) : DecidableEq (PoweredDart G) := Classical.decEq _

def selectors (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) (v : Preprocessing.Vertex G) :
    PoweringLabels.AddressSelector (Preprocessing.portGraph G)
      FinalConstants.walkLength v :=
  PoweringLabels.listSelector (Preprocessing.portGraph G) FinalConstants.walkLength
    v addresses complete

def powered (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) :
    ConstraintGraph (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet :=
  PoweringTest.poweredGraph (Preprocessing.portGraph G) (Preprocessing.graph G).accepts
    (2 * FinalConstants.endpointLength) (selectors addresses complete G)

abbrev Vertex (G : ConstraintGraph V E Label) :=
  QueryIncidence.Vertex
    (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet)
    (AlphabetGraph.Address (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet)

abbrev Dart (G : ConstraintGraph V E Label) :=
  QueryIncidence.Dart (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet) 6

instance (G : ConstraintGraph V E Label) : Fintype (Vertex G) := by
  letI : Fintype (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet) := inferInstance
  letI : Fintype
      (AlphabetGraph.Address (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet) :=
    inferInstance
  change Fintype
    (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet ⊕
      AlphabetGraph.Address (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet)
  infer_instance
instance (G : ConstraintGraph V E Label) : Fintype (Dart G) := by
  change Fintype ((AlphabetGraph.Event (PoweredDart G) PoweredAlphabet × Fin 6) × Bool)
  infer_instance
instance (G : ConstraintGraph V E Label) : DecidableEq (Vertex G) := Classical.decEq _

def graph (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) : ConstraintGraph (Vertex G) (Dart G) Label :=
  AlphabetGraph.graph (powered addresses complete G)

omit [Nonempty E] in
theorem powered_completeness (addresses : List Addresses)
    (complete : ∀ w, w ∈ addresses) (G : ConstraintGraph V E Label)
    (satisfied : G.Satisfiable) : (powered addresses complete G).Satisfiable := by
  obtain ⟨assignment, hassignment⟩ := Preprocessing.completeness G satisfied
  refine ⟨PoweringOpinions.honestLabels (Preprocessing.portGraph G)
    FinalConstants.walkLength assignment, ?_⟩
  apply PoweringTest.perfect_completeness (Preprocessing.portGraph G)
    (Preprocessing.graph G).accepts (2 * FinalConstants.endpointLength)
    (selectors addresses complete G) assignment
  intro e
  exact hassignment e

omit [Nonempty E] in
theorem completeness (addresses : List Addresses)
    (complete : ∀ w, w ∈ addresses) (G : ConstraintGraph V E Label)
    (satisfied : G.Satisfiable) : (graph addresses complete G).Satisfiable :=
  AlphabetGraph.perfect_completeness _
    (powered_completeness addresses complete G satisfied)

end UniqueGamesTheorem.Foundations.PCP.AmplificationRound

end

end

section

/-!
# The fixed constants in the actual powering estimate

The six-bit alphabet has 64 letters. The middle window, endpoint length,
spectral parameter and composition loss in the checked powering theorem give
exactly the constants used in the final amplification round. Large natural
constants remain symbolic in these calculations.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PoweringFinalConstants

abbrev Alphabet := Fin 6 → Bool

@[simp] theorem card_alphabet : Fintype.card Alphabet = 64 := by
  norm_num [Alphabet, Fintype.card_fun]

theorem card_alphabet_eq_final : Fintype.card Alphabet = FinalConstants.alphabet := by
  exact card_alphabet

/-- The actual six-bit alphabet gives the endpoint length fixed for the round. -/
theorem center_eq :
    PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf =
      FinalConstants.endpointLength := by
  rw [card_alphabet]
  rfl

/-- Prefix, pivot and suffix together have the fixed odd walk length. -/
theorem walkLength_eq :
    2 * PoweringSoundness.center (Fintype.card Alphabet) FinalConstants.windowHalf + 1 =
      FinalConstants.walkLength := by
  rw [center_eq]
  rfl

/-- The spectral denominator is exactly 66 at the fixed return parameter. -/
theorem spectral_denominator_eq :
    (1 + 2 / (1 - (31 / 32 : ℝ))) + 1 = 66 := by
  norm_num

/-- Dividing the actual powering coefficient by the composition loss gives
the round coefficient exactly. The large window parameter is not evaluated. -/
theorem gain_eq :
    PoweringSoundness.gain 64 FinalConstants.windowHalf (31 / 32) / 12288 =
      FinalConstants.gain := by
  change
    (1 / (2 * (FinalConstants.alphabet : ℝ))) ^ 4 *
        (FinalConstants.windowSize : ℝ) /
        ((1 + 2 / (1 - (31 / 32 : ℝ))) + 1) /
        (FinalConstants.compositionLoss : ℝ) =
      (FinalConstants.windowSize : ℝ) / (FinalConstants.denominator : ℝ)
  rw [spectral_denominator_eq]
  have hden : (FinalConstants.denominator : ℝ) =
      16 * (FinalConstants.alphabet : ℝ) ^ 4 * 66 *
        (FinalConstants.compositionLoss : ℝ) := by
    simp only [FinalConstants.denominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [hden]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem gain_card_eq :
    PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) /
        12288 = FinalConstants.gain := by
  rw [card_alphabet]
  exact gain_eq

/-- Both the coefficient and cap in the actual estimate match the fixed
round constants, for every real error parameter. -/
theorem scaled_bound_eq (ε : ℝ) :
    (PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) *
        min ε
          (1 / ((2 * PoweringSoundness.center (Fintype.card Alphabet)
            FinalConstants.windowHalf + 1 : Nat) : ℝ))) / 12288 =
      FinalConstants.gain * min ε FinalConstants.cap := by
  rw [walkLength_eq]
  rw [mul_div_right_comm, gain_card_eq]
  rfl

/-- The composed powering and alphabet-reduction coefficient yields the
fixed doubling bound after the checked preprocessing loss. -/
theorem composed_scaled_gap (ε : ℝ) (hε : 0 ≤ ε) :
    min (2 * ε) FinalConstants.cap ≤
      (PoweringSoundness.gain (Fintype.card Alphabet) FinalConstants.windowHalf (31 / 32) *
        min (ε / (Preprocessing.sizeFactor : ℝ))
          (1 / ((2 * PoweringSoundness.center (Fintype.card Alphabet)
            FinalConstants.windowHalf + 1 : Nat) : ℝ))) / 12288 := by
  rw [scaled_bound_eq]
  exact FinalConstants.composed_gap ε hε

end UniqueGamesTheorem.Foundations.PCP.PoweringFinalConstants

end

end OAI

import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Sum
import OAI.Computability.PerfectCompleteness.Algebra.MatrixInverseConstantsLemmas
import OAI.Computability.PerfectCompleteness.Machines.FixedUnaryRepresentationMachine
import OAI.Computability.UniqueGames.Machines.MachineCloudPadding

namespace OAI


namespace PerfectCompleteness.Completion

variable {L A B : Type*}

def fiberEquivTwo (e : A ≃ B × Fin 2) (b : B) :
    {a : A // (e a).1 = b} ≃ Fin 2 where
  toFun a := (e a.val).2
  invFun j := ⟨e.symm (b, j), by simp⟩
  left_inv a := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Prod.ext a.property.symm rfl
  right_inv j := by simp

theorem exists_slot_embedding [Fintype L] [Fintype B] [DecidableEq B]
    (p : L → B) (hsmall : ∀ b, Fintype.card {l : L // p l = b} ≤ 2) :
    ∃ slots : L ↪ B × Fin 2, ∀ l, (slots l).1 = p l := by
  classical
  have hslots (b : B) : Nonempty ({l : L // p l = b} ↪ Fin 2) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hsmall b)
  let fiberSlots (b : B) : {l : L // p l = b} ↪ Fin 2 :=
    Classical.choice (hslots b)
  let fiberMap : (Σ b : B, {l : L // p l = b}) ↪ Σ _ : B, Fin 2 :=
    Function.Embedding.sigmaMap (Function.Embedding.refl B) fiberSlots
  let slots : L ↪ B × Fin 2 :=
    (Equiv.sigmaFiberEquiv p).symm.toEmbedding.trans
      (fiberMap.trans (Equiv.sigmaEquivProd B (Fin 2)).toEmbedding)
  exact ⟨slots, fun _ => rfl⟩

theorem exists_exact_two_completion [Fintype L] [Fintype A] [Fintype B]
    [DecidableEq B] (legal : L ↪ A) (p : L → B)
    (hsmall : ∀ b, Fintype.card {l : L // p l = b} ≤ 2)
    (hcard : Fintype.card A = 2 * Fintype.card B) :
    ∃ pHat : A → B,
      (∀ l, pHat (legal l) = p l) ∧
      ∀ b, Fintype.card {a : A // pHat a = b} = 2 := by
  classical
  obtain ⟨slots, hslots⟩ := exists_slot_embedding p hsmall
  have hcardSlots : Fintype.card A = Fintype.card (B × Fin 2) := by
    rw [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]
    exact hcard
  let base : A ≃ B × Fin 2 := Fintype.equivOfCardEq hcardSlots
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun l : L => base (legal l)) (fun l : L => slots l)
    (base.injective.comp legal.injective) slots.injective
  let e : A ≃ B × Fin 2 := base.trans σ
  refine ⟨fun a => (e a).1, ?_, ?_⟩
  · intro l
    change (σ (base (legal l))).1 = p l
    rw [hσ l]
    exact hslots l
  · intro b
    exact (Fintype.card_congr (fiberEquivTwo e b)).trans (Fintype.card_fin 2)

end PerfectCompleteness.Completion



namespace PerfectCompleteness.FixedUnaryRepresentationPlacement


open Turing UniqueGamesTheorem.Foundations.Complexity
open MachineComposition MachineCloudPadding

abbrev Mode := FixedUnaryRepresentationMachine.Mode
abbrev Tape (width : Nat) := FixedUnaryRepresentationMachine.Tape width
abbrev Label (mode : Mode) (width : Nat) :=
  FixedUnaryRepresentationMachine.Label mode (List.finRange width)
abbrev CleanupLabel (width : Nat) := FixedUnaryRepresentationMachine.CleanupLabel width
abbrev State (A : Type) := A × Option Bool
abbrev Alphabet {K : Type} (_ : K) := Bool

variable {width : Nat} {K Λ A : Type}

def nativeProgram (mode : Mode) : Label mode width →
    TM2.Stmt (Alphabet (K := Tape width)) (Label mode width) (State A) :=
  FixedUnaryRepresentationMachine.instruction mode (List.finRange width) id none

def instruction (mode : Mode) (tape : Tape width → K)
    (labels : Label mode width → Λ) (exit : Option Λ) :
    Label mode width → TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  fun label => Placement.statement tape labels exit (nativeProgram mode label)

def entry (mode : Mode) (labels : Label mode width → Λ) (exit : Option Λ) : Option Λ :=
  Placement.label labels exit
    (FixedUnaryRepresentationMachine.entry mode (List.finRange width) id none)

def tapes (view : K → Option (Tape width)) (extra : K → List Bool)
    (mode : Mode) (values : Fin width → Nat) (destinations : Fin width → List Bool) :
    K → List Bool :=
  Placement.tapes view (FixedUnaryRepresentationMachine.stacks mode values destinations) extra

theorem tapes_eq_base (tape : Tape width → K) (view : K → Option (Tape width))
    (right : ∀ j k, view j = some k → tape k = j) (base : K → List Bool)
    (mode : Mode) (values : Fin width → Nat) (destinations : Fin width → List Bool)
    (contents : ∀ k, base (tape k) =
      FixedUnaryRepresentationMachine.stacks mode values destinations k) :
    tapes view base mode values destinations = base := by
  funext j
  cases viewed : view j with
  | none => simp only [tapes, Placement.tapes, viewed]
  | some k =>
      simp only [tapes, Placement.tapes, viewed]
      rw [← right j k viewed]
      exact (contents k).symm

def cleanupNativeProgram : CleanupLabel width →
    TM2.Stmt (Alphabet (K := Tape width)) (CleanupLabel width) (State A) :=
  FixedUnaryRepresentationMachine.cleanupInstruction id none

def cleanupInstruction (tape : Tape width → K)
    (labels : CleanupLabel width → Λ) (exit : Option Λ) :
    CleanupLabel width → TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  fun label => Placement.statement tape labels exit (cleanupNativeProgram label)

def cleanupEntry (labels : CleanupLabel width → Λ) (exit : Option Λ) : Option Λ :=
  Placement.label labels exit (FixedUnaryRepresentationMachine.cleanupEntry id none)

variable [DecidableEq K]

theorem familyTrace (mode : Mode) (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label mode width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction mode tape labels exit label)
    (extra : K → List Bool) (values : Fin width → Nat)
    (destinations : Fin width → List Bool) (ambient : A) :
    (advance (TM2.step program))^[FixedUnaryRepresentationMachine.steps mode values (List.finRange width)]
      (some ⟨entry mode labels exit, (ambient, none), tapes view extra mode values destinations⟩) =
      some ⟨exit, (ambient, none), tapes view extra mode values
        (fun position => FixedUnaryRepresentationMachine.targetWord mode (values position) ++
          destinations position)⟩ := by
  have native := FixedUnaryRepresentationMachine.familyTrace mode values id none
    (nativeProgram (width := width) (A := A) mode) (fun _ => rfl) destinations ambient
  have placed := Placement.trace tape view left right labels exit extra
    (nativeProgram (width := width) (A := A) mode) program atLabels _ _ _ native
  simpa only [Placement.configuration, Placement.label, entry, tapes] using placed

def familyInTime (mode : Mode) (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : Label mode width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = instruction mode tape labels exit label)
    (extra : K → List Bool) (values : Fin width → Nat)
    (destinations : Fin width → List Bool) (ambient : A)
    (maximum : Nat) (bounded : ∀ position, values position ≤ maximum) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨entry mode labels exit, (ambient, none), tapes view extra mode values destinations⟩
      (some ⟨exit, (ambient, none), tapes view extra mode values
        (fun position => FixedUnaryRepresentationMachine.targetWord mode (values position) ++
          destinations position)⟩)
      (width * (2 * maximum + 3)) where
  steps := FixedUnaryRepresentationMachine.steps mode values (List.finRange width)
  evals_in_steps := familyTrace mode tape view left right labels exit program atLabels extra
    values destinations ambient
  steps_le_m := by
    simpa only [List.length_finRange] using
      FixedUnaryRepresentationMachine.steps_le mode values (List.finRange width) maximum bounded

theorem cleanupTrace (mode : Mode) (tape : Tape width → K) (view : K → Option (Tape width))
    (left : ∀ k, view (tape k) = some k)
    (right : ∀ j k, view j = some k → tape k = j)
    (labels : CleanupLabel width → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ label, program (labels label) = cleanupInstruction tape labels exit label)
    (extra : K → List Bool) (values : Fin width → Nat)
    (destinations : Fin width → List Bool) (ambient : A) :
    (advance (TM2.step program))^[MachineDrainMany.steps
      (FixedUnaryRepresentationMachine.cleanupTapes width)
      (FixedUnaryRepresentationMachine.stacks mode values destinations)]
      (some ⟨cleanupEntry labels exit, (ambient, none), tapes view extra mode values destinations⟩) =
      some ⟨exit, (ambient, none), tapes view extra mode values (fun _ => [])⟩ := by
  have native := FixedUnaryRepresentationMachine.cleanupTrace mode values id none
    (cleanupNativeProgram (width := width) (A := A)) (fun _ => rfl) destinations ambient
  have placed := Placement.trace tape view left right labels exit extra
    (cleanupNativeProgram (width := width) (A := A)) program atLabels _ _ _ native
  simpa only [Placement.configuration, Placement.label, cleanupEntry, tapes] using placed

end PerfectCompleteness.FixedUnaryRepresentationPlacement



namespace PerfectCompleteness.InitialParameters

open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

noncomputable section

def epsilon (δ : ℚ) : ℝ := (δ : ℝ) / 3
def simultaneous (δ : ℚ) : ℝ := epsilon δ ^ 2 / 2
def useful (δ : ℚ) : ℝ := simultaneous δ / 2
def inverse (δ : ℚ) : ℝ := simultaneous δ ^ 2 / 32

theorem epsilon_pos {δ : ℚ} (hδ : 0 < δ) : 0 < epsilon δ := by
  have : (0 : ℝ) < δ := by exact_mod_cast hδ
  unfold epsilon
  positivity

theorem simultaneous_pos {δ : ℚ} (hδ : 0 < δ) : 0 < simultaneous δ := by
  have := epsilon_pos hδ
  unfold simultaneous
  positivity

theorem useful_pos {δ : ℚ} (hδ : 0 < δ) : 0 < useful δ := by
  have := simultaneous_pos hδ
  unfold useful
  positivity

theorem inverse_pos {δ : ℚ} (hδ : 0 < δ) : 0 < inverse δ := by
  have := simultaneous_pos hδ
  unfold inverse
  positivity

theorem epsilon_lt_one {δ : ℚ} (hδ : δ < 1) : epsilon δ < 1 := by
  have : (δ : ℝ) < 1 := by exact_mod_cast hδ
  unfold epsilon
  linarith

theorem exists_initial {δ : ℚ} (hδ : 0 < δ) (hδ' : δ < 1) :
    ∃ depth r : Nat, 2 ≤ depth ∧ 4 ≤ (depth : ℝ) * epsilon δ ∧
      1 ≤ r ∧ ∃ α : ℝ, 0 < α ∧ α < 1 ∧
        MatrixLevelBridge.levelCutoffConstant r α + RankLevelFilter.node (r + 1) <
          inverse δ / 2 := by
  have hε := epsilon_pos hδ
  have hε' := epsilon_lt_one hδ'
  obtain ⟨depth, hdepth⟩ := exists_nat_gt (4 / epsilon δ + 2)
  have hd2 : (2 : ℝ) < depth := by
    have := div_pos (by norm_num : (0 : ℝ) < 4) hε
    linarith
  have hd : 2 ≤ depth := by exact_mod_cast hd2.le
  have hmul : 4 ≤ (depth : ℝ) * epsilon δ := by
    have hdiv : 4 / epsilon δ < (depth : ℝ) := by linarith
    exact ((div_lt_iff₀ hε).mp hdiv).le
  obtain ⟨r, hr, α, hα, hα', hcut⟩ :=
    MatrixInverseConstants.exists_cutoff_density
      (show 0 < inverse δ / 2 by have := inverse_pos hδ; positivity)
  exact ⟨depth, r, hd, hmul, hr, α, hα, hα', hcut⟩

end
end PerfectCompleteness.InitialParameters

end OAI

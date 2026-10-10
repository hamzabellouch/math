import OAI.Computability.UniqueGames.Machines.MachineCanonicalOutputLemmas
import OAI.Computability.UniqueGames.Machines.MachinePaddedExpanderFamilyBoundsLemmas
import OAI.Computability.UniqueGames.Machines.MachinePaddedOverlay
import OAI.Computability.UniqueGames.Machines.MachineRegularInternalRow
import OAI.Computability.UniqueGames.Machines.MachineRegularMetadata
import OAI.Computability.UniqueGames.PCP.PreprocessingRegularLoopWordsLemmas

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime

open Turing
open PCP
open MachinePaddedOverlay (BaseTable Tape Label State)

def rawProgram (H : BaseTable) (d : Nat) (hd : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .inl .original
  output := .inr (.inr MachineOverlayTable.output)
  main := MachinePaddedOverlay.main
  initial := MachinePaddedOverlay.clean H d hd
  code := MachinePaddedOverlay.program H d hd

theorem sourceMachine_eq (H : BaseTable) (d : Nat) (hd : 0 < d) :
    MachineCanonicalOutput.sourceMachine (rawProgram H d hd) =
      MachinePaddedOverlay.machine H d hd := rfl

/-- A fixed finite list of every non-output stack. This includes both
retained archives, the original input, and the physically consumed level. -/
noncomputable def cleanupTapes : List Tape :=
  (Finset.univ.erase (.inr (.inr MachineOverlayTable.output) : Tape)).toList

theorem cleanup_complete (H : BaseTable) (d : Nat) (hd : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram H d hd).output := by
  simp [cleanupTapes, rawProgram]

theorem initial_configuration (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    initList (MachineCanonicalOutput.sourceMachine (rawProgram H d hd))
        (PortTables.inputBits a) =
      ⟨some MachinePaddedOverlay.main, MachinePaddedOverlay.clean H d hd,
        MachinePaddedOverlay.initialTapes a.2⟩ := by
  change initList (MachinePaddedOverlay.machine H d hd) (PortTables.tableBits a.2) = _
  exact MachinePaddedOverlay.initial_configuration H hd a.2

/-- The raw terminal witness is the actual three-phase execution. No phase
trace, output-size bound, or complexity assertion is an input hypothesis. -/
noncomputable def terminalRun (H : BaseTable) (d : Nat) (hd : 0 < d)
    (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram H d hd) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.paddedOverlay H d a))
      ((MachinePaddedOverlay.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachinePaddedOverlay.clean H d hd
  tapes := MachinePaddedOverlay.finalTapes H a.2
  execution := by
    rw [initial_configuration]
    exact MachinePaddedOverlay.execution H hd a.2
  output_eq := MachinePaddedOverlay.final_output H hd a.2

/-- A concrete machine reaches the canonical `haltList` encoding of the
existing executable preprocessing map in polynomial time. -/
noncomputable def computableInPolyTime (H : BaseTable) (d : Nat) (hd : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := d + MachinePaddedOverlay.overlayDegree))
      (PreprocessingStageMaps.paddedOverlay H d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

/-- Finiteness belongs to the exact machine stored in the certificate above. -/
theorem finite_alphabet (H : BaseTable) (d : Nat) (hd : 0 < d) :
    ∀ k, Finite ((computableInPolyTime H d hd).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram H d hd) cleanupTapes
    (cleanup_complete H d hd) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.paddedOverlay H d) (MachinePaddedOverlay.timePolynomial d)
    (terminalRun H d hd)

end UniqueGamesTheorem.Foundations.Complexity.MachinePaddedOverlayRuntime

/-! Polynomial bounds for the actual regularization subcalls. These lemmas
bound the established step counts; they do not assume any machine execution. -/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineRegularExecutionBounds

open Turing MachineComposition PCP PCP.PreprocessingRegularTables PCP.PreprocessingCloudIndex
open PCP.PreprocessingMachineBounds MachineRegularInternalRow

theorem coreTimeBound_mono (q L R x v i k o m O L' R' x' v' i' k' o' m' O' : Nat)
    (hL : L ≤ L') (hR : R ≤ R') (hx : x ≤ x') (hv : v ≤ v') (hi : i ≤ i')
    (hk : k ≤ k') (ho : o ≤ o') (hm : m ≤ m') (hO : O ≤ O') :
    coreTimeBound q L R x v i k o m O ≤ coreTimeBound q L' R' x' v' i' k' o' m' O' := by
  unfold coreTimeBound
  gcongr

noncomputable def corePolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C (5*q+32) * rotorPolynomial q + 10 * Polynomial.X +
    2 * (Polynomial.C ExpanderFamily.growth * Polynomial.X) + 13 * Polynomial.X +
    5 * Polynomial.X + Polynomial.C (5*q+10) *
      (Polynomial.X + Polynomial.C ExpanderFamily.growth * Polynomial.X) +
    4 * (Polynomial.C ExpanderFamily.growth * Polynomial.X) +
    2 * regularPolynomial + Polynomial.C (8*q+41066)

theorem corePolynomial_eval (q L : Nat) :
    (corePolynomial q).eval L =
      coreTimeBound q L ((rotorPolynomial q).eval L)
        (ExpanderFamily.growth*L) L (ExpanderFamily.growth*L) L
        (ExpanderFamily.growth*L) L (regularPolynomial.eval L) := by
  simp only [corePolynomial, coreTimeBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]
  omega

theorem internal_steps_le (q : Nat) (positive : 0 < q) (t : GraphTables.Table)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding t v) q)
    (v : Fin t.vertices) (x : PaddedCloud t (padding t) v) (p : Fin q)
    (outputLength : Nat) (houtput : outputLength ≤ regularPolynomial.eval (inputLength t)) :
    coreSteps t (padding t) tables v x p outputLength ≤
      (corePolynomial q).eval (inputLength t) := by
  have hx : (vertexOrder t (padding t) x.val).val ≤ ExpanderFamily.growth * inputLength t :=
    (vertexOrder t (padding t) x.val).isLt.le.trans (regularVertices_le_input t)
  have hi : (paddedCloudRank t (padding t) v x).val ≤ ExpanderFamily.growth * inputLength t :=
    (paddedCloudRank t (padding t) v x).isLt.le.trans (cloudTotal_le_input t v)
  have hv : v.val ≤ inputLength t :=
    v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  rw [corePolynomial_eval]
  exact (coreSteps_le q positive t (padding t) tables v x p outputLength).trans
    (coreTimeBound_mono q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ le_rfl
      (cloudRotorBits_le t v (tables v)) hx hv hi (cloudSize_le_input t v)
      (prefix_le_input t v.val) hm houtput)

noncomputable def familyPolynomial : Polynomial Nat :=
  MachinePaddedExpanderFamilyBounds.timePolynomial.comp (Polynomial.X + 1) +
    Polynomial.C (2 * ExpanderFamily.growth) * (Polynomial.X + 1) + 7

/-- The completed reusable family call includes the three actual drains. -/
theorem family_budget_le (t : GraphTables.Table) (v : Fin t.vertices) :
    MachinePaddedExpanderFamilyBounds.timePolynomial.eval (cloudSize t v + 1) +
      2 * ExpanderFamily.growth * (cloudSize t v + 1) + 7 ≤
        familyPolynomial.eval (inputLength t) := by
  have h := Nat.add_le_add_right (cloudSize_le_input t v) 1
  have hp := natPolynomial_eval_mono MachinePaddedExpanderFamilyBounds.timePolynomial h
  have hm := Nat.mul_le_mul_left (2 * ExpanderFamily.growth) h
  simp only [familyPolynomial, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  omega

/-- A generous serialized-row bound evaluated at the actual linear vertex cap. -/
noncomputable def rowPolynomial (q : Nat) : Polynomial Nat :=
  Polynomial.C ExpanderFamily.growth * Polynomial.X +
    (Polynomial.C ExpanderFamily.growth * Polynomial.X) * Polynomial.C (q + 1) + 8192

theorem rowPolynomial_eval (q L : Nat) :
    (rowPolynomial q).eval L =
      ExpanderFamily.growth * L + (ExpanderFamily.growth * L) * (q + 1) + 8192 := by
  simp only [rowPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat]

theorem actual_row_bound_le (q : Nat) (t : GraphTables.Table) :
    vertexCount t (padding t) + vertexCount t (padding t) * (q + 1) + 8192 ≤
      (rowPolynomial q).eval (inputLength t) := by
  rw [rowPolynomial_eval]
  have h := regularVertices_le_input t
  exact Nat.add_le_add_right (Nat.add_le_add h (Nat.mul_le_mul_right _ h)) _

/-- The inner port loop can grow the old prefix by at most `q` complete rows. -/
noncomputable def blockCorePolynomial (q : Nat) : Polynomial Nat :=
  corePolynomial q + Polynomial.C (2*q) * rowPolynomial q

theorem coreTimeBound_add_output (q L R x v i k o m O A : Nat) :
    coreTimeBound q L R x v i k o m (O + A) =
      coreTimeBound q L R x v i k o m O + 2*A := by
  unfold coreTimeBound
  omega

/-- Uniform cap for the actual affine bound used by the port-loop wrapper,
including all rows it may already have appended during this vertex. -/
theorem block_core_bound_le (q : Nat) (t : GraphTables.Table)
    (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding t v) q)
    (v : Fin t.vertices) (x : PaddedCloud t (padding t) v)
    (initialOutput : Nat) (houtput : initialOutput ≤ regularPolynomial.eval (inputLength t)) :
    coreTimeBound q (GraphTables.tableBits t).length
      (encodeWords (ExpanderTableWords.rotationWords (tables v))).length
      (vertexOrder t (padding t) x.val).val v.val (paddedCloudRank t (padding t) v x).val
      (cloudSize t v) (PreprocessingPaddingOffsets.offset (padding t) v.val) t.darts
      (initialOutput + q *
        (vertexCount t (padding t) + vertexCount t (padding t) * (q + 1) + 8192)) ≤
      (blockCorePolynomial q).eval (inputLength t) := by
  have hx : (vertexOrder t (padding t) x.val).val ≤ ExpanderFamily.growth * inputLength t :=
    (vertexOrder t (padding t) x.val).isLt.le.trans (regularVertices_le_input t)
  have hi : (paddedCloudRank t (padding t) v x).val ≤ ExpanderFamily.growth * inputLength t :=
    (paddedCloudRank t (padding t) v x).isLt.le.trans (cloudTotal_le_input t v)
  have hv : v.val ≤ inputLength t :=
    v.isLt.le.trans (GraphTables.vertices_le_tableBits_length t)
  have hm : t.darts ≤ inputLength t := GraphTables.darts_le_tableBits_length t
  have hr := Nat.mul_le_mul_left q (actual_row_bound_le q t)
  have hO := Nat.add_le_add houtput hr
  have h := coreTimeBound_mono q (inputLength t) _ _ _ _ _ _ _ _
    (inputLength t) _ _ _ _ _ _ _ _ le_rfl
    (cloudRotorBits_le t v (tables v)) hx hv hi (cloudSize_le_input t v)
    (prefix_le_input t v.val) hm hO
  simp only [coreTimeBound_add_output] at h ⊢
  rw [← corePolynomial_eval] at h
  simpa only [inputLength, blockCorePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Nat.mul_assoc] using h

end UniqueGamesTheorem.Foundations.Complexity.MachineRegularExecutionBounds

end OAI

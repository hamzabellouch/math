import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FixedInterpreter
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TM0AlternatingPresentation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.TM0LatticePresentation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RapidMachineDecisionInput

namespace OAI

/-! All three rapid-forcing decision inputs follow from Mathlib's halting
theorem. The universal machine is fixed; its program argument is encoded
in the finite input word. -/

namespace ForcedComputation

open FiniteMachine

private theorem list_val_computable (n : ℕ) :
    Computable (fun w : List (Fin n) => w.map Fin.val) :=
  (Primrec.list_map Primrec.id
    ((Primrec.dom_finite Fin.val).comp Primrec.snd).to₂).to_comp

theorem rapidMachineHaltingUndecidable : RapidMachineHaltingUndecidable := by
  rintro ⟨d, hd, hcorrect⟩
  obtain ⟨g, q, M, input, hi, hM⟩ := exists_fixed_universal_TM0
  have hc : Computable (fun n => (rapidTM0 M).inputDescription (input n)) :=
    Computable.encode.comp ((Computable.const _).pair
      ((list_val_computable _).comp hi))
  apply ComputablePred.halting_problem 0
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun c : Nat.Partrec.Code => d ((rapidTM0 M).inputDescription
    (input (Encodable.encode c))), hd.comp (hc.comp Computable.encode), ?_⟩
  funext c
  apply propext
  have h := (hcorrect (rapidTM0 M) (input (Encodable.encode c))).trans
    ((rapidTM0_halts_iff M _).trans (hM _))
  simpa only [Denumerable.ofNat_encode] using h.symm

theorem alternatingMachineHaltingUndecidable : AlternatingMachineHaltingUndecidable := by
  rintro ⟨d, hd, hcorrect⟩
  obtain ⟨g, q, M, input, hi, hM⟩ := exists_fixed_universal_TM0
  have hc : Computable (fun n => (alternatingTM0 M, (input n).map Fin.val)) :=
    (Computable.const _).pair ((list_val_computable _).comp hi)
  apply ComputablePred.halting_problem 0
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun c : Nat.Partrec.Code => d (alternatingTM0 M,
    (input (Encodable.encode c)).map Fin.val), hd.comp (hc.comp Computable.encode), ?_⟩
  funext c
  apply propext
  have hv : (alternatingTM0 M).ValidInput ((input (Encodable.encode c)).map Fin.val) := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact b.isLt
  have h := (hcorrect (alternatingTM0 M) _ (alternatingTM0_wellFormed M) hv).trans
    ((alternatingTM0_halts_iff M _).trans (hM _))
  simpa only [Denumerable.ofNat_encode] using h.symm

private theorem lattice_constructor_computable (M : PeriodicLattice.Machine) :
    Computable (fun w : List ℕ => (⟨M, w⟩ : PeriodicLattice.Input)) := by
  apply Computable.encode_iff.mp
  change Computable (fun w : List ℕ => Encodable.encode (M, w))
  exact Computable.encode.comp ((Computable.const M).pair Computable.id)

private theorem lattice_input_computable (R : RapidForcing.Machine) :
    Computable (fun w : R.Input =>
      (⟨latticeMachine R, w.map Fin.val⟩ : PeriodicLattice.Input)) :=
  (lattice_constructor_computable (latticeMachine R)).comp (list_val_computable R.symbols)

private theorem lattice_input_valid (R : RapidForcing.Machine) (w : R.Input) :
    (⟨latticeMachine R, w.map Fin.val⟩ : PeriodicLattice.Input).WellFormed := by
  refine ⟨latticeMachine_wellFormed R, ?_⟩
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact b.isLt

private theorem lattice_undecidable_of_universal (R : RapidForcing.Machine)
    (input : ℕ → R.Input) (hi : Computable input)
    (hM : ∀ n, R.Halts (input n) ↔
      ((Denumerable.ofNat Nat.Partrec.Code n).eval 0).Dom) :
    LatticeMachineHaltingUndecidable := by
  rintro ⟨d, hd, hcorrect⟩
  have hc := (lattice_input_computable R).comp hi
  apply ComputablePred.halting_problem 0
  apply ComputablePred.computable_iff.mpr
  refine ⟨fun c : Nat.Partrec.Code => d
    ⟨latticeMachine R, (input (Encodable.encode c)).map Fin.val⟩,
    hd.comp (hc.comp Computable.encode), ?_⟩
  funext c
  apply propext
  have h := (hcorrect
    ⟨latticeMachine R, (input (Encodable.encode c)).map Fin.val⟩
    (lattice_input_valid R (input (Encodable.encode c)))).trans
    ((latticeMachine_halts_iff R (input (Encodable.encode c))).trans
      (hM (Encodable.encode c)))
  simpa only [Denumerable.ofNat_encode] using h.symm

theorem latticeMachineHaltingUndecidable : LatticeMachineHaltingUndecidable := by
  obtain ⟨g, q, M, input, hi, hM⟩ := exists_fixed_universal_TM0
  apply lattice_undecidable_of_universal (rapidTM0 M) input hi
  intro n
  exact (rapidTM0_halts_iff M (input n)).trans (hM n)

end ForcedComputation

end OAI

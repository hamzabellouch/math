import Mathlib
import OAI.Computability.QuantumFactoring.RetainedQuarterFilter
import OAI.Computability.QuantumFactoring.ZeroOutside

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BooleanNetwork BitArithmetic Exactness
namespace PhysicalTree

lemma actual_quarter_mass {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x=>(quarterFlag n (by omega)).eval x 0=true)
      ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N)))=1/4 := by
  rw [quarterProgram_state,outcomeMass_encode _ (quarterEncoding_injective n N)]
  have he : ((fun x=>(quarterFlag n (by omega)).eval x 0=true) ∘ quarterEncoding n N)=
      Quarter.passed N (paddedAccepted (N:=N) (by omega)) := by
    funext r
    exact propext (quarterFlag_eval hn hN hb r)
  rw [he]
  exact quarter_mass hn hN hb

def reflectWork (n : ℕ) (hn : 0<n) : ℕ :=
  max (quarterFlag n hn).net.count (zeroNet n).net.count
abbrev amplifiedWidth (n : ℕ) (hn : 0<n) := quarterWidth n+1+reflectWork n hn

def amplifiedProgram (n : ℕ) (hn : 0<n) : List (Instruction (amplifiedWidth n hn)) :=
  amplificationProgram (quarterProgram n) (quarterFlag n hn) (zeroNet n)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
def amplifiedZero (n N : ℕ) (hn : 0<n) : Basis (amplifiedWidth n hn) :=
  packed (reflectWork n hn) (quarterZero n N) (fun _=>false)
def amplifiedOutput (n : ℕ) (hn : 0<n) : BooleanNetwork (amplifiedWidth n hn) (n*n) :=
  (select (firstRegister (quarterWidth n) 1 (reflectWork n hn))).comp (quarterOutputNet n)

/-- An unconditional physical amplification identity for the actual program.
The only hypotheses are the manuscript's padded length and valid input. -/
theorem amplifiedProgram_state {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    (programMatrix (amplifiedProgram n (by omega))).mulVec
      (basisVector (amplifiedZero n N (by omega))) =
      encodeState (fun x=>packed (reflectWork n (by omega)) x (fun _ : Fin 1=>false))
        (fun x=> -2*goodPart (fun y=>(quarterFlag n (by omega)).eval y 0=true)
          ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) x) := by
  apply physical_quarter_amplification _ _ _ _ _
    (inputSector (inputWires n) (quarterZero n N))
    (quarterProgram_respects_input n N) _
  · intro _ _; rfl
  · exact zeroNet_sector n N
  · exact actual_quarter_mass hn hN hb

lemma prepared_nonzero_encoding {n N : ℕ} (x : Basis (quarterWidth n))
    (hx : ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) x≠0) :
    ∃ r : Quarter.Raw (PaddedRaw n) n, quarterEncoding n N r=x := by
  classical
  rw [quarterProgram_state] at hx
  by_contra hh
  exact hx (encodeState_outside _ _ x hh)

lemma quarterFlag_output_on_support {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (x : Basis (quarterWidth n))
    (hx : ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) x≠0)
    (hp : (quarterFlag n (by omega)).eval x 0=true) :
    CorrectEncoding N n (guessWords n ((quarterOutputNet n).eval x)) := by
  obtain ⟨r,rfl⟩:=prepared_nonzero_encoding x hx
  rw [quarterOutputNet_eval]
  exact quarter_output hn hN hb r ((quarterFlag_eval hn hN hb r).mp hp)

/-- Exact support on complete sorted factorizations, for the actual finite
fixed-gate program and a literal Boolean readout. This is a necessary main
proof dependency, not the missing polynomial/uniform circuit-family theorem. -/
theorem amplified_output_on_support {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (x : Basis (amplifiedWidth n (by omega)))
    (hx : ((programMatrix (amplifiedProgram n (by omega))).mulVec
      (basisVector (amplifiedZero n N (by omega)))) x≠0) :
    CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x)) := by
  classical
  rw [amplifiedProgram_state hn hN hb] at hx
  have hr : ∃ y : Basis (quarterWidth n),
      packed (reflectWork n (by omega)) y (fun _ : Fin 1=>false)=x := by
    by_contra hh
    exact hx (encodeState_outside _ _ x hh)
  obtain ⟨y,rfl⟩:=hr
  rw [encodeState_at _ (packed_injective _)] at hx
  have hg : goodPart (fun z=>(quarterFlag n (by omega)).eval z 0=true)
      ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) y≠0 := by
    intro h; exact hx (by rw [h,mul_zero])
  have hp : (quarterFlag n (by omega)).eval y 0=true := by
    by_contra hp
    exact hg (by simp only [goodPart,ite_eq_right hp])
  have hy : ((programMatrix (quarterProgram n)).mulVec (basisVector (quarterZero n N))) y≠0 := by
    simpa only [goodPart,ite_eq_left hp] using hg
  have he : (amplifiedOutput n (by omega)).eval
      (packed (reflectWork n (by omega)) y (fun _ : Fin 1=>false))=(quarterOutputNet n).eval y := by
    rw [amplifiedOutput,eval_comp,eval_select,packed_first]
  rw [he]
  exact quarterFlag_output_on_support hn hN hb y hy hp

lemma amplified_mass_one {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x=>CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x)))
      ((programMatrix (amplifiedProgram n (by omega))).mulVec
        (basisVector (amplifiedZero n N (by omega))))=1 := by
  classical
  have he : ∀ x : Basis (amplifiedWidth n (by omega)),
      (if CorrectEncoding N n (guessWords n ((amplifiedOutput n (by omega)).eval x)) then
        Complex.normSq (((programMatrix (amplifiedProgram n (by omega))).mulVec
          (basisVector (amplifiedZero n N (by omega)))) x) else 0)=
        Complex.normSq (((programMatrix (amplifiedProgram n (by omega))).mulVec
          (basisVector (amplifiedZero n N (by omega)))) x) := by
    intro x
    by_cases hx : ((programMatrix (amplifiedProgram n (by omega))).mulVec
      (basisVector (amplifiedZero n N (by omega)))) x=0
    · simp only [hx,Complex.normSq_zero,ite_self]
    · rw [ite_eq_left (amplified_output_on_support hn hN hb x hx)]
  simp_rw [outcomeMass,he]
  rw [unitary_mass _ (programMatrix_unitary _)]
  simp [basisVector]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

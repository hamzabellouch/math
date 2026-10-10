import Mathlib
import OAI.Computability.QuantumFactoring.RetainedTreeFilter
import OAI.Computability.QuantumFactoring.TreeRootOutput
import OAI.Computability.QuantumFactoring.TreeQuarterPhysical

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic OrderTrial
namespace PhysicalTree

def launchHistory (n : ℕ) : BooleanNetwork (launchWidth n) (width n) :=
  select (targetRegister n (width n) (launchWork n))
def launchInput (n : ℕ) : BooleanNetwork (launchWidth n) n :=
  select (firstRegister n (width n) (launchWork n))
def paddedHistory (n : ℕ) : BooleanNetwork (paddedWidth n) (width n) :=
  (select (Fin.castAdd (tensorWidth n (padding n)))).comp (launchHistory n)
def paddedInput (n : ℕ) : BooleanNetwork (paddedWidth n) n :=
  (select (Fin.castAdd (tensorWidth n (padding n)))).comp (launchInput n)
def paddedPad (n : ℕ) : BooleanNetwork (paddedWidth n) (tensorWidth n (padding n)) :=
  select (Fin.natAdd (launchWidth n))

lemma paddedHistory_eval (n N : ℕ) (r : PaddedRaw n) :
    (paddedHistory n).eval (paddedEncoding n N r)=
      (machine n).encoded (initialQueue n N) (2*n^2) r.1 := by
  simp only [paddedHistory,eval_comp,eval_select,Function.comp_def,paddedEncoding,
    Fin.append_left,launchHistory,launchEncoding]
  exact packed_targetRegister _ _
lemma paddedInput_eval (n N : ℕ) (r : PaddedRaw n) :
    (paddedInput n).eval (paddedEncoding n N r)=natBasis n N := by
  simp only [paddedInput,eval_comp,eval_select,Function.comp_def,paddedEncoding,
    Fin.append_left,launchInput,launchEncoding]
  exact packed_first _ _
lemma paddedPad_eval (n N : ℕ) (r : PaddedRaw n) :
    (paddedPad n).eval (paddedEncoding n N r)=tensorLayout n (padding n) r.2 := by
  funext i
  simp only [paddedPad,eval_select,Function.comp_apply,paddedEncoding,Fin.append_right]

def padFlag (n : ℕ) : BooleanNetwork (tensorWidth n (padding n)) 1 :=
  all (List.ofFn (fun i : Fin (padding n)=>(zeroWord (tensorSelect n (padding n) i)).bnot))
lemma padFlag_eval (n : ℕ) (r : PadRaw n) :
    (padFlag n).eval (tensorLayout n (padding n) r) 0=true ↔ padPassed r := by
  simp only [padFlag,all_eval,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,
    bnot_value,zeroWord_value,tensorSelect_eval,padPassed,Completion.rare]

def paddedFlag (n : ℕ) (hn : 0<n) : BooleanNetwork (paddedWidth n) 1 :=
  ((paddedHistory n).comp ((machine n).acceptedNet hn (2*n^2))).band
    ((paddedPad n).comp (padFlag n))
lemma paddedFlag_eval {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : PaddedRaw n) :
    (paddedFlag n (by omega)).eval (paddedEncoding n N r) 0=true ↔
      paddedAccepted (N:=N) (by omega) r := by
  rw [paddedFlag,eval_band,Bool.and_eq_true,eval_comp,paddedHistory_eval,
    acceptedNet_iff_accepted hn hN hb,eval_comp,paddedPad_eval,padFlag_eval]
  rfl

def quarterOrd (n : ℕ) := Completion.ordinaryWires (paddedWidth n) (n*n) 1 (n^11)
def quarterGuess (n : ℕ) := Completion.guessWires (paddedWidth n) (n*n) 1 (n^11)
def quarterCoin (n : ℕ) := Completion.retentionWires (paddedWidth n) (n*n) 1 (n^11)
def quarterRare (n : ℕ) := Completion.rareNet (paddedWidth n) (n*n) 1 (n^11)

lemma quarterOrd_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterOrd n).eval (quarterEncoding n N r)=paddedEncoding n N r.2.1 :=
  Completion.ordinaryWires_eval (r.1,paddedEncoding n N r.2.1,r.2.2)
lemma quarterGuess_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterGuess n).eval (quarterEncoding n N r)=r.2.2.1 :=
  Completion.guessWires_eval (r.1,paddedEncoding n N r.2.1,r.2.2)
lemma quarterCoin_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterCoin n).eval (quarterEncoding n N r)=r.2.2.2 :=
  Completion.retentionWires_eval (r.1,paddedEncoding n N r.2.1,r.2.2)
lemma quarterRare_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterRare n).eval (quarterEncoding n N r) 0=true ↔ Completion.rare r.1 :=
  Completion.rareNet_eval (r.1,paddedEncoding n N r.2.1,r.2.2)

def quarterKeep (n : ℕ) (p : ℚ) : BooleanNetwork (quarterWidth n) 1 :=
  retentionNet (Quarter.D n) (.const p) (.var ()) (fun _ : Unit=>quarterCoin n)
lemma quarterKeep_eval (n N : ℕ) (p : ℚ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterKeep n p).eval (quarterEncoding n N r) 0=true ↔
      Completion.threshold p r.2.2.2 := by
  rw [quarterKeep,retentionNet_value]
  simp only [RatExpr.eval_const,NatExpr.eval,quarterCoin_eval,Completion.threshold]

def quarterGuessFlag (n : ℕ) : BooleanNetwork (quarterWidth n) 1 :=
  ((((quarterOrd n).comp (paddedInput n)).pair (quarterGuess n))).comp (guessVerifier n)
lemma quarterGuessFlag_eval {n N : ℕ} (hn : 128≤n) (hb : N<2^n)
    (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterGuessFlag n).eval (quarterEncoding n N r) 0=true ↔
      CorrectEncoding N n (guessWords n r.2.2.1) := by
  rw [quarterGuessFlag,eval_comp,eval_pair,eval_comp,quarterOrd_eval,paddedInput_eval,
    quarterGuess_eval,guessVerifier_correct hn,natBasis_value,Nat.mod_eq_of_lt hb]

def quarterFlag (n : ℕ) (hn : 0<n) : BooleanNetwork (quarterWidth n) 1 :=
  ((quarterRare n).bnot.band
    (((quarterOrd n).comp (paddedFlag n hn)).band (quarterKeep n (Quarter.retention n)))).bor
    ((quarterRare n).band ((quarterGuessFlag n).band (quarterKeep n (Quarter.guessRetention n))))

/-- The literal Boolean flag for the source's exact quarter event. All factor
and order tests read the actual retained history, not an ideal initialized table. -/
theorem quarterFlag_eval {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterFlag n (by omega)).eval (quarterEncoding n N r) 0=true ↔
      Quarter.passed N (paddedAccepted (N:=N) (by omega)) r := by
  simp only [quarterFlag,eval_bor,Bool.or_eq_true,eval_band,Bool.and_eq_true,
    bnot_value,quarterRare_eval,eval_comp,quarterOrd_eval,
    paddedFlag_eval hn hN hb,quarterKeep_eval,quarterGuessFlag_eval hn hb,
    Quarter.passed,Quarter.ordinaryPass,Quarter.guessPass]

def paddedOutputNet (n : ℕ) : BooleanNetwork (paddedWidth n) (n*n) :=
  (paddedHistory n).comp (rootFlat n (2*n^2))
def quarterOutputNet (n : ℕ) : BooleanNetwork (quarterWidth n) (n*n) :=
  Completion.outputNet (paddedOutputNet n) 1 (n^11)
lemma quarterOutputNet_eval (n N : ℕ) (r : Quarter.Raw (PaddedRaw n) n) :
    (quarterOutputNet n).eval (quarterEncoding n N r)=
      Completion.output (ordinaryOutput n N) r := by
  rw [quarterOutputNet]
  change (Completion.outputNet (paddedOutputNet n) 1 (n^11)).eval
    (Completion.layout _ _ _ _ (r.1,paddedEncoding n N r.2.1,r.2.2))=_
  rw [Completion.outputNet_eval]
  simp only [Completion.output,paddedOutputNet,eval_comp,paddedHistory_eval,ordinaryOutput]

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

import Mathlib
import OAI.Computability.QuantumFactoring.VerifiedRoot
import OAI.Computability.QuantumFactoring.TreePadding
import OAI.Computability.QuantumFactoring.QuarterPreparation

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

/-- Only a fixed rearrangement of output wires, from tensor grouping to the
source's consecutive n-bit fields. No factor search is present. -/
def flattenWords (n : ℕ) : BooleanNetwork (tensorWidth n n) (n*n) :=
  wordBlocks (fun i=>tensorSelect n n i)

lemma flattenWords_numbers {n : ℕ} (zs : List (Basis n)) (hl : zs.length=n) :
    guessWords n ((flattenWords n).eval (SortedWords.layout n n zs))=SortedWords.numbers zs := by
  let f : Fin n→Basis n := fun i=>zs[i.val]'(by omega)
  have hf : List.ofFn f=zs := by
    apply List.ext_getElem
    · simp only [List.length_ofFn,hl]
    · intro i hi hj
      simp only [List.getElem_ofFn,f]
  rw [←hf,SortedWords.layout_ofFn]
  simp only [guessWords,flattenWords,wordBlocks_eval,tensorSelect_eval,
    SortedWords.numbers,List.map_ofFn,Function.comp_def]

/-- A literal bounded readout for every clock count, with a harmless zero case. -/
def rootFlat (n : ℕ) : (t : ℕ)→BooleanNetwork ((machine n).width t) (n*n)
  | 0=>Completion.zeros _ _
  | t+1=>(rootResult n t).comp (flattenWords n)

lemma rootFlat_correct {n N : ℕ} (hN : 2≤N) (hb : N<2^n)
    (t : ℕ) (h : NodeMachine.Trace n (t+1))
    (hv : (machine n).verified (initialQueue n N) (t+1) h) :
    CorrectEncoding N n (guessWords n ((rootFlat n (t+1)).eval
      ((machine n).encoded (initialQueue n N) (t+1) h))) := by
  obtain ⟨zs,hl,hc,he⟩:=verified_root hN hb t h hv
  rw [rootFlat,eval_comp,he,flattenWords_numbers zs hl]
  exact hc

noncomputable def ordinaryOutput (n N : ℕ) (r : PaddedRaw n) : Basis (n*n) :=
  (rootFlat n (2*n^2)).eval ((machine n).encoded (initialQueue n N) (2*n^2) r.1)

/-- Soundness uses verifier success on this raw history, not ideal quantum
success or an externally supplied prime-factorization list. -/
theorem padded_output {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : PaddedRaw n) (hp : paddedAccepted (N:=N) (by omega) r) :
    CorrectEncoding N n (guessWords n (ordinaryOutput n N r)) := by
  have hh : ∀ (t : ℕ) (h : NodeMachine.Trace n t), 0<t →
      (machine n).verified (initialQueue n N) t h →
      CorrectEncoding N n (guessWords n ((rootFlat n t).eval
        ((machine n).encoded (initialQueue n N) t h))) := by
    intro t
    cases t with
    | zero=>intro _ ht; omega
    | succ t=>intro h _ hv; exact rootFlat_correct hN hb t h hv
  apply hh _ _ _ hp.1.1
  have : 0<n := by omega
  positivity

/-- Both branches of Section 6's final quarter-probability preparation now
use the actual chronological tree. This is an event/output theorem; it does
not assert the missing efficient Boolean implementation of the full flag. -/
theorem quarter_mass {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (Quarter.passed N (paddedAccepted (n:=n) (N:=N) (by omega)))
      (Quarter.fresh (paddedState n N) n)=1/4 := by
  exact Quarter.passed_mass hn hN hb _ _ (padded_normalized n N) (padded_mass hn hN hb)

theorem quarter_output {n N : ℕ} (hn : 128≤n) (hN : 2≤N) (hb : N<2^n)
    (r : Quarter.Raw (PaddedRaw n) n)
    (hp : Quarter.passed N (paddedAccepted (n:=n) (N:=N) (by omega)) r) :
    CorrectEncoding N n (guessWords n (Completion.output (ordinaryOutput n N) r)) :=
  Quarter.passed_correct _ _ (fun r hr=>padded_output hn hN hb r hr) r hp

end PhysicalTree
end ExactQuantumFactoring


end

end OAI

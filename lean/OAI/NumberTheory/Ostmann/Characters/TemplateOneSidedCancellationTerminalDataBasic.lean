import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSourcePairActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedRelabel
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairWeight

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval TemplateOneSidedBudget
open TemplateOneSidedRelabel ParityActions OneSidedPhase Preliminaries
open HigherBiasSource.SourceTemplate TemplateOneSidedSupportTelescoping
attribute [local instance] Classical.propDecidable

def terminalIntegerState (k n : ℕ) (width : Role → ℕ) (m : ℕ)
    (hm : m ≤ width .word) (σ : Reassignments k n m)
    (x : (schedule k (n+1)).Constituent width → ℤ) : State k (n+1) :=
  fun i=>∏a : Fin (width ((schedule k (n+1)).role i)),
    x ((prefixConstituentPermutation k n width m hm σ).symm ⟨i,a⟩)

 theorem paritySampledExpressions_integer_eval (k n : ℕ) (width : Role → ℕ) (m : ℕ)
    (hm : m ≤ width .word) (σ : Reassignments k n m)
    (x : (schedule k (n+1)).Constituent width → ℤ) :
    evalExpressions x (paritySampledExpressions k n width m hm σ) =
      terminalIntegerState k n width m hm σ x := by
  rw [paritySampledExpressions,permutedSampledExpressions,relabelExpressions_eval,
    sampledExpressions_eval]
  rfl

 theorem terminalIntegerState_prime {Q : ℕ} (k n : ℕ) (width : Role → ℕ) (m : ℕ)
    (hm : m ≤ width .word) (σ : Reassignments k n m)
    (x : (schedule k (n+1)).Constituent width → PrimeUpTo Q) :
    terminalIntegerState k n width m hm σ (fun i=>(x i).val) =
      constituentSampleState (schedule k (n+1)) width
        (constituentAssignment (schedule k (n+1)) width
          (prefixConstituentPermutation k n width m hm σ) x) := by
  rw [← paritySampledExpressions_integer_eval]
  exact paritySampledExpressions_prime_eval k n width m hm σ x

theorem terminal_initial_expression_parameters (k n : ℕ) (width : Role → ℕ) (m : ℕ)
    (hm : m ≤ width .word) (σ : Reassignments k n m) (N : ℕ) (hw : ∀q,width q ≤ N)
    {H : ℝ} (hH : 0 ≤ H) :
    (∀x i,HistoryReconstruction.Good x (paritySampledExpressions k n width m hm σ i)) ∧
    (∀i,(paritySampledExpressions k n width m hm σ i).syntaxSize ≤ 2*(N+1)) ∧
    (∀i,(paritySampledExpressions k n width m hm σ i).FixedLogBound H) := by
  refine ⟨permutedSampledExpressions_good k (n+1) width _,?_,?_⟩
  · intro i
    exact (permutedSampledExpressions_syntaxSize k (n+1) width _ i).trans
      (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (hw _) 1))
  · exact permutedSampledExpressions_fixedBound k (n+1) width _
      (Real.one_le_exp_iff.mpr hH)

def terminalCorePairAmplitude (k n : ℕ) (width : Role → ℕ) (m : ℕ)
    (hm : m ≤ width .word) (B V : ℕ → ℤ) (T : ℕ → ℝ) (J s v : ℤ)
    (σ π : Reassignments k n m) (t u : HistoryReconstruction.Tree (n+1))
    (gate : Bool) (X Δ Wp Wl : ℝ)
    (x : (schedule k (n+1)).Constituent width → ℤ) : ℂ :=
  if gate then
    conj (coreHistoryWeight k (fun l _=>B l) (fun l _=>V l)
      (canonicalHistoryExtra k (fun l=>pivotWindow (T l) Wp))
      (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ Wl))
      X Δ Wl (n+1) s (terminalIntegerState k n width m hm σ x) t) *
    coreHistoryWeight k (fun l _=>B l) (fun l _=>V l)
      (canonicalHistoryExtra k (fun l=>pivotWindow (T l) Wp))
      (canonicalHistoryMask k (sourceRangeLeafMask k J X Δ Wl))
      X Δ Wl (n+1) v (terminalIntegerState k n width m hm π x) u
  else 0

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI

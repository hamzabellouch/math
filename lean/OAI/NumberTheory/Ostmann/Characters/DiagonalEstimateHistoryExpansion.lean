import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateMass
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateRootPairs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

section
variable {I H K : Type*} [Fintype I] [Fintype H] [Fintype K]
    [DecidableEq I] [DecidableEq K] {Q : ℕ}
    (E : I → Finset (PrimeUpTo Q)) (hE : ∀i,0<primeShellMass (E i))
    (A : Finset (Equiv.Perm I)) (root : H → K) (F : (I → PrimeUpTo Q) → H → ℂ)

theorem matchedRootContribution_grouped_history :
    matchedRootContribution E hE A (fun f s=>∑h,if root h=s then F f h else 0) =
    let μ := productPrior (fun i=>primeShellPrior (E i) (hE i))
    ∑e∈A,∑f,((μ.mass f*μ.mass (f∘e):ℝ):ℂ)*
      (∑h,∑h',if root h'=root h then F f h*conj (F (f∘e) h') else 0) := by
  unfold matchedRootContribution
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  simp only [mul_assoc]
  rw [←Finset.mul_sum,finite_root_pairing]

def normalizedHistoryPair (T D : ℝ) (e : Equiv.Perm I) (h h' : H) : ℂ :=
  (productPrior (fun i=>primeShellPrior (E i) (hE i))).cmean (fun f=>
    (((Real.exp (T+D)/((∏i,(f i).val:ℕ):ℝ))*
      ∏i,if f (e i)∈E i then (1:ℝ) else 0):ℝ) *
      (if root h'=root h then F f h*conj (F (f∘e) h') else 0))

theorem matchedRootContribution_eq_normalized_history (T D : ℝ) :
    matchedRootContribution E hE A (fun f s=>∑h,if root h=s then F f h else 0) =
      ((copiedNormalization E*Real.exp (-T-D):ℝ):ℂ)*
        ∑e∈A,∑h,∑h',normalizedHistoryPair E hE root F T D e h h' := by
  rw [matchedRootContribution_grouped_history]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp_rw [matched_mass_factorization E hE _ e T D]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h' hh'
  simp only [normalizedHistoryPair,FinitePrior.cmean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  simp only [Complex.ofReal_mul]
  ring

end
end Ostmann.Characters.DiagonalEstimate

end

end OAI

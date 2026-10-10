import OAI.NumberTheory.TotientAsymptotic.ActualComparison
import OAI.NumberTheory.TotientAsymptotic.FordKernel

namespace OAI

/-! The bound for one fixed class of actual tuple pairs, including both tails. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

/-- Fix the surviving indices, the common and canceled primes, the grid and
one residual integer. The published Ford estimate then bounds actual pairs,
with both residual tuple factorizations included in the saving. -/
theorem actual_comparison_class_kernel (hford : FordLemma51Input) :
    ∃ C y₀ : ℝ, 0 < C ∧ 1 < y₀ ∧
    ∀ {x t y S h : ℝ} {H k K D r : ℕ} (I : Finset ℕ) (Y U : ℕ → ℝ),
      y₀ ≤ y → 1 ≤ Real.log y → 0 < B y → 5 ≤ h →
      ((R x H-k : ℕ) : ℝ) ≤ h → (I.card : ℝ) ≤ h →
      Real.log (B y) ≤ 26*h →
      (D.primeFactorsList.length : ℝ) ≤ 2*B y/h^8 → (K : ℝ) ≤ 2*B y/h^8 →
      1 < Y I.card → 0 ≤ B (Y I.card) → B (Y I.card) ≤ 2*B y/h^18 →
      FordComparisonParameters I.card y S D r Y U →
      (-2+(∑ j ∈ Finset.Icc 1 (I.card-1), a j*(B (Y j)/B y))+
        comparisonError I.card y S Y U ≤ -1-1/(2*h^4)) →
      L x H < m x → R x H < L x H → k < L x H →
      ∀ Q : Finset (TotientTuple (R x H) × TotientTuple (R x H)),
      (∀ q ∈ Q, IsBasicTuple x H t q.1 ∧ IsBasicTuple x H t q.2) →
      ∀ fixed : ℕ → ℕ × ℕ,
      (∀ q ∈ Q, ∀ j ≤ k, j ∉ I →
        wholeWitnessPrime q.1.head (chosenRemainder x H q.1.tail) j=(fixed j).1 ∧
        wholeWitnessPrime q.2.head (chosenRemainder x H q.2.tail) j=(fixed j).2) →
      (∀ q ∈ Q, (suffixPreimage (chosenRemainder x H q.1.tail) k).totient=D) →
      (∀ q ∈ Q, (comparisonPairAt x H k I q).remainder.primeFactorsList.length ≤ K) →
      (∀ q ∈ Q, FordComparisonConditions I.card y S D r Y U (comparisonPairAt x H k I q)) →
      (Q.card : ℝ) ≤ y/(D*r)/Real.log y*
        Real.exp (6*(|Real.log C|+26)*h^2-B y/(4*h^4)) := by
  obtain ⟨C,y₀,hC,hy₀,hbound⟩ := actual_comparison_with_recovery hford
  refine ⟨C,y₀,hC,hy₀,?_⟩
  intro x t y S h H k K D r I Y U hy hlog hBy hh hn hb hlogB hD hK hT hZ hZu
    hparam hE hL hR hk Q hQ fixed hfixed hres hrem hcond
  have hDr : 0 < D*r := Nat.mul_pos hparam.2.2.2.2.2.2.2.1
    hparam.2.2.2.2.2.2.2.2.2.2.1
  exact (hbound I y S Y U hy hparam hL hR hk Q hQ fixed hfixed hres hrem hcond).trans
    (ford_recovered_kernel hC (hy₀.trans_le hy) hlog hBy hh hn hb hlogB hD hK hT hZ hZu hDr hE)

end TotientAsymptotic

end

end OAI

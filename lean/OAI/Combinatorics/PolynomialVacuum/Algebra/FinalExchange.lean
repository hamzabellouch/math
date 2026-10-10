import OAI.Combinatorics.PolynomialVacuum.Algebra.DiscrepancyRoots
import OAI.Combinatorics.PolynomialVacuum.Algebra.ZeroSpectatorPair

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

 

theorem finalExchange_of_cups {n : ℕ} (hn : 2≤n) (Ψ : State (n+2)) (ψ : State n)
    (hex : LowerExchange (liftState Ψ) (n+1))
    (hexψ : LowerExchange (liftState ψ) n)
    (hnode : NaturalCupNodes (liftState Ψ) (liftState ψ) n)
    (hc : ∀ i≤n, CupAt (liftState Ψ) (liftState ψ) n i)
    (hd : ∀ s i, (Ψ s).degreeOf i≤n+1)
    (hp : ∀ s i, s i=Spin.plus → (Ψ s).degreeOf i≤n) (hz : MinusZero Ψ) :
    ∀ Y, siteR n (Y n) (Y (n+1)) (liftState Ψ Y)=
      exchangeDenominator (Y n) (Y (n+1)) • liftState Ψ (swapSite n Y) := by
  apply (exchangeDiscrepancy_zero_iff Ψ n).mp
  apply polynomial_zero_of_two_zero_spins
  · have hf (j : ℕ) (hj : j<n) (s : ℕ → Spin) (hs : s j≠Spin.zero) :
        exchangeDiscrepancy Ψ n s=0 := by
      cases he : s j with
      | zero => exact (hs he).elim
      | plus => exact exchangeDiscrepancy_plus_zero Ψ ψ hex hexψ hnode hc hp hj s he
      | minus => exact exchangeDiscrepancy_minus_zero Ψ ψ hex hexψ hnode hc hd hz hj s he
    intro s hs
    rcases hs with hs|hs
    · exact hf 0 (by omega) s hs
    · exact hf 1 (by omega) s hs
  · intro Y
    have he := exchangeDifference_exchanges hex 0 (by omega) Y
    have heval (X : ℕ → ℂ) : (fun s => eval X (exchangeDiscrepancy Ψ n s))=
        exchangeDifference (liftState Ψ) n X := by
      funext s
      exact eval_exchangeDiscrepancy Ψ n s X
    simpa only [heval] using he

theorem fullExchange_of_cups {n : ℕ} (hn : 2≤n) (Ψ : State (n+2)) (ψ : State n)
    (hex : LowerExchange (liftState Ψ) (n+1))
    (hexψ : LowerExchange (liftState ψ) n)
    (hnode : NaturalCupNodes (liftState Ψ) (liftState ψ) n)
    (hc : ∀ i≤n, CupAt (liftState Ψ) (liftState ψ) n i)
    (hd : ∀ s i, (Ψ s).degreeOf i≤n+1)
    (hp : ∀ s i, s i=Spin.plus → (Ψ s).degreeOf i≤n) (hz : MinusZero Ψ) :
    LowerExchange (liftState Ψ) (n+2) := by
  intro j hj
  by_cases h : j+1<n+1
  · exact hex j h
  · have he : j=n := by omega
    subst j
    exact finalExchange_of_cups hn Ψ ψ hex hexψ hnode hc hd hp hz

end PolynomialVacuumAlgebra

end OAI

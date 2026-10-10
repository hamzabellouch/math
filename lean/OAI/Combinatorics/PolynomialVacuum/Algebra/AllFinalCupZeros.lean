import OAI.Combinatorics.PolynomialVacuum.Algebra.FinalCupZeros

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem cupZero_transport_generic {D : NatSpectralTensor} {n i k : ℕ}
    (hex : LowerExchange D n) (hik : i < k) (hk : k < n)
    (hc : ∀ X, X (i+1)=T*X i → D X=0)
    (X : ℕ → ℂ) (hX : X k=T*X i)
    (hG : trainDenominator (T*X i) X (i+1) (k-i-1)≠0) : D X=0 := by
  have he := braidTrain_pull_exchange hex (i+1) (k-i-1) (by omega) (T*X i) X
  rw [show i+1+(k-i-1)=k by omega,← hX,Function.update_eq_self] at he
  rw [hX] at he
  rw [hc _ (by simp [pullSite_before (by omega : i < i+1)]),map_zero] at he
  exact (smul_right_injective _ hG) (he.symm.trans (smul_zero _).symm)

theorem exchangeDifference_spectatorCup {n i k : ℕ} (Ψ : State (n+2)) (ψ : State n)
    (hex : LowerExchange (liftState Ψ) (n+1))
    (hexψ : LowerExchange (liftState ψ) n)
    (hik : i < k) (hk : k < n) (hc : CupAt (liftState Ψ) (liftState ψ) n i)
    (X : ℕ → ℂ) (hX : X k=T*X i) : exchangeDifference (liftState Ψ) n X=0 := by
  funext s
  have he : cupSpecialize i k (exchangeDiscrepancy Ψ n s)=cupSpecialize i k 0 := by
    apply cupSurface_eq_of_generic i k (by omega) _ _ (partialTrainGuard k i) (partialTrainGuard_surface hik)
    intro Y hY hG
    have hz := cupZero_transport_generic (exchangeDifference_exchanges hex) hik hk
      (exchangeDifference_adjacentCup (by omega) hexψ hc) Y hY (by simpa using hG)
    simpa only [eval_exchangeDiscrepancy,map_zero,exchangeDifference,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using congrFun hz s
  have he' := eval_eq_of_cupSurface_eq i k _ _ he X hX
  simpa only [eval_exchangeDiscrepancy,map_zero,exchangeDifference,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using he'

 

theorem exchangeDifference_cup_zero {n : ℕ} (Ψ : State (n+2)) (ψ : State n)
    (hex : LowerExchange (liftState Ψ) (n+1))
    (hexψ : LowerExchange (liftState ψ) n)
    (hnode : NaturalCupNodes (liftState Ψ) (liftState ψ) n)
    (hc : ∀ i≤n, CupAt (liftState Ψ) (liftState ψ) n i)
    (i k : ℕ) (hi : i < n) (hik : i < k) (hk : k < n+2)
    (X : ℕ → ℂ) (hX : X k=T*X i) : exchangeDifference (liftState Ψ) n X=0 := by
  by_cases h : k < n
  · exact exchangeDifference_spectatorCup Ψ ψ hex hexψ hik h (hc i (by omega)) X hX
  · by_cases h' : k=n
    · subst k
      exact finalDifference_penultimate Ψ ψ hex hnode hi (hc i (by omega)) X hX
    · have h' : k=n+1 := by omega
      subst k
      exact finalDifference_last Ψ ψ hex hnode hi (hc i (by omega)) X hX

end PolynomialVacuumAlgebra

end OAI

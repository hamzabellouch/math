import OAI.Combinatorics.PolynomialVacuum.Algebra.ExchangeDifference
import OAI.Combinatorics.PolynomialVacuum.Algebra.LastDegrees
import OAI.Combinatorics.PolynomialVacuum.Algebra.InterpolatedZero

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem exchangeDiscrepancy_spectator_degree {n d j : ℕ} (Ψ : State (n+2))
    (hj : j < n) (s : ℕ → Spin)
    (hd : ∀ u : Fin (n+2) → Spin, u ⟨j,by omega⟩=s j → (Ψ u).degreeOf ⟨j,by omega⟩ ≤ d) :
    (exchangeDiscrepancy Ψ n s).degreeOf j ≤ d := by
  have hdeg (u : ℕ → Spin) (hu : u j=s j) : (coordinatePolynomial Ψ u).degreeOf j ≤ d := by
    rw [coordinatePolynomial_degree Ψ u ⟨j,by omega⟩]
    exact hd _ hu
  have hx : (X n : MvPolynomial ℕ ℂ).degreeOf j ≤ 0 := by simp [degreeOf_X_of_ne (by omega : j≠n)]
  have hy : (X (n+1) : MvPolynomial ℕ ℂ).degreeOf j ≤ 0 := by simp [degreeOf_X_of_ne (by omega : j≠n+1)]
  have hden : (polyExchangeDenominator (X n) (X (n+1)) : MvPolynomial ℕ ℂ).degreeOf j ≤ 0 := by
    unfold polyExchangeDenominator
    have hb (a : ℂ) : (C a*X n-X (n+1) : MvPolynomial ℕ ℂ).degreeOf j ≤ 0 := by
      exact (degreeOf_sub_le _ _ _).trans (max_le (dconst_mul a hx) hy)
    simpa only [Nat.zero_add] using dmul (hb (t^2)) (hb T)
  unfold exchangeDiscrepancy
  apply (degreeOf_sub_le _ _ _).trans
  apply max_le
  · apply (degreeOf_sum_le _ _ _).trans
    apply Finset.sup_le
    intro ab _
    exact (dmul (polyExchange_degree _ _ _ ab j 0 hx hy)
      (hdeg _ (replacePair_other s (by omega) (by omega) ab))).trans (by omega)
  · have hr : (rename (Equiv.swap n (n+1)) (coordinatePolynomial Ψ s)).degreeOf j=
        (coordinatePolynomial Ψ s).degreeOf j := by
      simpa only [Equiv.swap_apply_of_ne_of_ne (by omega : j≠n) (by omega : j≠n+1)] using
        (degreeOf_rename_of_injective (Equiv.swap n (n+1)).injective j (p:=coordinatePolynomial Ψ s))
    exact (dmul hden (hr ▸ hdeg s rfl)).trans (by omega)

theorem eval_liftState_minusZero {N : ℕ} (Ψ : State N) (hz : MinusZero Ψ)
    (j : ℕ) (hj : j < N) (s : ℕ → Spin) (X : ℕ → ℂ)
    (hs : s j=Spin.minus) (hX : X j=0) : liftState Ψ X s=0 := by
  have he := congrArg (eval (fun k : Fin N => X k.val)) (hz (fun k => s k.val) ⟨j,hj⟩ hs)
  simp only [eval_killSite,map_zero] at he
  have hh : Function.update (fun k : Fin N => X k.val) ⟨j,hj⟩ 0=(fun k : Fin N => X k.val) := by
    rw [← hX]
    exact Function.update_eq_self _ _
  have hh' : @Function.update (Fin N) (fun _ => ℂ) (Classical.decEq _) (fun k => X k.val) ⟨j,hj⟩ 0=(fun k => X k.val) := by
    funext k
    by_cases h : k=⟨j,hj⟩
    · subst k; simp [hX]
    · simp [h]
  simpa only [hh',liftState,liftPolyTensor] using he

theorem exchangeDiscrepancy_spectator_minus_zero {n j : ℕ} (Ψ : State (n+2))
    (hj : j < n) (hz : MinusZero Ψ) (s : ℕ → Spin) (hs : s j=Spin.minus)
    (X : ℕ → ℂ) (hX : X j=0) : eval X (exchangeDiscrepancy Ψ n s)=0 := by
  rw [eval_exchangeDiscrepancy]
  have hr : liftState Ψ (swapSite n X) s=0 :=
    eval_liftState_minusZero Ψ hz j (by omega) s _ hs
      (by simpa only [swapSite_other (by omega : j≠n) (by omega : j≠n+1)] using hX)
  rw [hr,mul_zero,sub_zero]
  change (∑ ab : Pair, exchangeNumerator (X n) (X (n+1)) (s n,s (n+1)) ab *
    liftState Ψ X (replacePair s n (n+1) ab))=0
  apply Finset.sum_eq_zero
  intro ab _
  rw [eval_liftState_minusZero Ψ hz j (by omega) _ X
    (by simpa only [replacePair_other _ (by omega : j≠n) (by omega : j≠n+1)] using hs) hX,mul_zero]

end PolynomialVacuumAlgebra

end OAI

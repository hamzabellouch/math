import OAI.Combinatorics.PolynomialVacuum.Algebra.AllFinalCupZeros
import OAI.Combinatorics.PolynomialVacuum.Algebra.ScaledRootGuard
import OAI.Combinatorics.PolynomialVacuum.Algebra.ExchangeDiscrepancyBounds

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def cupRootScale (j k : ℕ) : ℂ := if k<j then T else T⁻¹

theorem cupRootScale_ne_zero (j k : ℕ) : cupRootScale j k≠0 := by
  unfold cupRootScale
  split_ifs <;> simp [T_ne_zero]

theorem exchangeDiscrepancy_root {n j : ℕ} (Ψ : State (n+2)) (ψ : State n)
    (hex : LowerExchange (liftState Ψ) (n+1))
    (hexψ : LowerExchange (liftState ψ) n)
    (hnode : NaturalCupNodes (liftState Ψ) (liftState ψ) n)
    (hc : ∀ i≤n, CupAt (liftState Ψ) (liftState ψ) n i)
    (hj : j < n) (s : ℕ → Spin) (Y : ℕ → ℂ) (k : ℕ)
    (hk : k∈(Finset.range (n+2)).erase j) :
    eval (Function.update Y j (cupRootScale j k*Y k)) (exchangeDiscrepancy Ψ n s)=0 := by
  obtain ⟨hkj,hk⟩ := Finset.mem_erase.mp hk
  have hk' := Finset.mem_range.mp hk
  let Z := Function.update Y j (cupRootScale j k*Y k)
  have hkZ : Z k=Y k := Function.update_of_ne hkj _ _
  have hjZ : Z j=cupRootScale j k*Y k := by simp [Z]
  have he : exchangeDifference (liftState Ψ) n Z=0 := by
    by_cases h : k<j
    · apply exchangeDifference_cup_zero Ψ ψ hex hexψ hnode hc k j (by omega) h (by omega) Z
      rw [hjZ,hkZ,cupRootScale,ite_eq_left h]
    · apply exchangeDifference_cup_zero Ψ ψ hex hexψ hnode hc j k hj (by omega) hk' Z
      rw [hkZ,hjZ,cupRootScale,ite_eq_right h]
      simp [T_ne_zero]
  simpa only [eval_exchangeDiscrepancy,exchangeDifference,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,Pi.zero_apply] using congrFun he s

theorem exchangeDiscrepancy_plus_zero {n j : ℕ} (Ψ : State (n+2)) (ψ : State n)
    (hex : LowerExchange (liftState Ψ) (n+1))
    (hexψ : LowerExchange (liftState ψ) n)
    (hnode : NaturalCupNodes (liftState Ψ) (liftState ψ) n)
    (hc : ∀ i≤n, CupAt (liftState Ψ) (liftState ψ) n i)
    (hp : ∀ s i, s i=Spin.plus → (Ψ s).degreeOf i≤n)
    (hj : j<n) (s : ℕ → Spin) (hs : s j=Spin.plus) : exchangeDiscrepancy Ψ n s=0 := by
  apply polynomial_zero_of_scaled_roots j ((Finset.range (n+2)).erase j) (cupRootScale j)
    (by intro k _; exact cupRootScale_ne_zero j k)
  · have hd := exchangeDiscrepancy_spectator_degree Ψ hj s
      (fun u hu => hp u ⟨j,by omega⟩ (hu.trans hs))
    have hcard : ((Finset.range (n+2)).erase j).card=n+1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)),Finset.card_range]
      omega
    rw [hcard]
    omega
  · exact exchangeDiscrepancy_root Ψ ψ hex hexψ hnode hc hj s

theorem exchangeDiscrepancy_minus_zero {n j : ℕ} (Ψ : State (n+2)) (ψ : State n)
    (hex : LowerExchange (liftState Ψ) (n+1))
    (hexψ : LowerExchange (liftState ψ) n)
    (hnode : NaturalCupNodes (liftState Ψ) (liftState ψ) n)
    (hc : ∀ i≤n, CupAt (liftState Ψ) (liftState ψ) n i)
    (hd : ∀ s i, (Ψ s).degreeOf i≤n+1) (hz : MinusZero Ψ)
    (hj : j<n) (s : ℕ → Spin) (hs : s j=Spin.minus) : exchangeDiscrepancy Ψ n s=0 := by
  apply polynomial_zero_of_scaled_roots_zero j ((Finset.range (n+2)).erase j) (cupRootScale j)
    (by intro k _; exact cupRootScale_ne_zero j k)
  · have hdeg := exchangeDiscrepancy_spectator_degree Ψ hj s (fun u _ => hd u _)
    have hcard : ((Finset.range (n+2)).erase j).card=n+1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)),Finset.card_range]
      omega
    rwa [hcard]
  · intro Y
    exact exchangeDiscrepancy_spectator_minus_zero Ψ hj hz s hs _ (by simp)
  · exact exchangeDiscrepancy_root Ψ ψ hex hexψ hnode hc hj s

end PolynomialVacuumAlgebra

end OAI

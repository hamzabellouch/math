import OAI.Combinatorics.PolynomialVacuum.Algebra.ExchangeDiscrepancy

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

noncomputable def exchangeDifference (Ψ : NatSpectralTensor) (n : ℕ) : NatSpectralTensor :=
  fun X => siteR n (X n) (X (n+1)) (Ψ X)-
    exchangeDenominator (X n) (X (n+1)) • Ψ (swapSite n X)

theorem swapSite_comm {α : Type*} {i j : ℕ} (h : i+1 < j) (X : ℕ → α) :
    swapSite i (swapSite j X)=swapSite j (swapSite i X) := by
  funext k
  simp only [swapSite,Function.comp_apply,Equiv.swap_apply_def]
  split_ifs <;> congr 1 <;> omega

theorem exchangeDifference_exchanges {Ψ : NatSpectralTensor} {n : ℕ}
    (hΨ : LowerExchange Ψ (n+1)) : LowerExchange (exchangeDifference Ψ n) n := by
  intro j hj X
  have h0 : swapSite j X n=X n := swapSite_other (by omega) (by omega) X
  have h1 : swapSite j X (n+1)=X (n+1) := swapSite_other (by omega) (by omega) X
  have h2 : swapSite n X j=X j := swapSite_other (by omega) (by omega) X
  have h3 : swapSite n X (j+1)=X (j+1) := swapSite_other (by omega) (by omega) X
  have he := hΨ j (by omega) (swapSite n X)
  rw [h2,h3,swapSite_comm hj X] at he
  simp only [exchangeDifference,map_sub,map_smul,h0,h1]
  rw [← Module.End.mul_apply,siteR_far_comm (Or.inl hj),Module.End.mul_apply,
    hΨ j (by omega) X,map_smul,he,smul_sub,smul_smul,smul_smul]
  rw [mul_comm (exchangeDenominator (X n) (X (n+1)))]

theorem skipTwo_swap_after {α : Type*} {i j : ℕ} (h : i+2 ≤ j) (X : ℕ → α) :
    skipTwo i (swapSite j X)=swapSite (j-2) (skipTwo i X) := by
  funext k
  simp only [skipTwo,swapSite,Function.comp_apply,Equiv.swap_apply_def]
  split_ifs <;> congr 1 <;> omega

theorem fusionProduct_swap {j m : ℕ} (hj : j+1 < m) (a : ℂ) (X : ℕ → ℂ) :
    fusionProduct a (swapSite j X) m=fusionProduct a X m := by
  unfold fusionProduct
  apply Finset.prod_equiv (Equiv.swap j (j+1))
  · intro k
    simp only [Finset.mem_range,Equiv.swap_apply_def]
    split_ifs <;> omega
  · intro k hk
    rfl

theorem exchangeDifference_adjacentCup {Ψ ψ : NatSpectralTensor} {n i : ℕ}
    (hi : i+1 < n) (hexψ : LowerExchange ψ n)
    (hc : CupAt Ψ ψ n i) (X : ℕ → ℂ) (hX : X (i+1)=T*X i) :
    exchangeDifference Ψ n X=0 := by
  have h0 : swapSite n X i=X i := swapSite_other (by omega) (by omega) X
  have h1 : swapSite n X (i+1)=X (i+1) := swapSite_other (by omega) (by omega) X
  have hs : skipTwo i (swapSite n X)=swapSite (n-2) (skipTwo i X) := skipTwo_swap_after (by omega) X
  have hf : naturalFusion n i (swapSite n X)=naturalFusion n i X := by
    simp only [naturalFusion,h0,hs,fusionProduct_swap (by omega : n-2+1 < n)]
  have he := hexψ (n-2) (by omega) (skipTwo i X)
  have hy0 : skipTwo i X (n-2)=X n := by simp [skipTwo,show ¬n-2 < i by omega,show n-2+2=n by omega]
  have hy1 : skipTwo i X (n-2+1)=X (n+1) := by simp [skipTwo,show ¬n-2+1 < i by omega,show n-2+1+2=n+1 by omega]
  rw [hy0,hy1] at he
  rw [exchangeDifference,hc X hX,hc (swapSite n X) (by simpa only [h0,h1] using hX),hf,map_smul,
    ← Module.End.mul_apply,siteR_cup_after (by omega),Module.End.mul_apply,he,map_smul,hs]
  simp only [smul_smul,mul_comm,sub_self]

end PolynomialVacuumAlgebra

end OAI

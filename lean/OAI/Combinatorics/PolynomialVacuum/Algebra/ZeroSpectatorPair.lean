import OAI.Combinatorics.PolynomialVacuum.Algebra.ExchangeDifference

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem offdiagonal_zero_pair_nonzero : exchangeNumerator 0 1 (.minus,.plus) (.zero,.zero)≠0 := by
  rw [numerator_entry_7_0]
  simp only [sq,mul_zero,zero_add,mul_one]
  rw [show q-q^5=q*(1-Complex.I) by rw [show q^5=q*q^4 by ring,q_pow_four]; ring]
  exact mul_ne_zero q_ne_zero (by exact sub_ne_zero.mpr (by intro h; have := congrArg Complex.im h; norm_num at this))

theorem siteR_zero_pair (W : SpinTensor ℕ ℂ) (x y : ℂ) (s : ℕ → Spin)
    (h0 : s 0=Spin.zero) (h1 : s 1=Spin.zero)
    (hW : ∀ u, u 0≠Spin.zero ∨ u 1≠Spin.zero → W u=0) :
    siteR 0 x y W (replacePair s 0 1 (.minus,.plus))=
      exchangeNumerator x y (.minus,.plus) (.zero,.zero)*W s := by
  change (∑ ab : Pair, exchangeNumerator x y
    (replacePair s 0 1 (.minus,.plus) 0,replacePair s 0 1 (.minus,.plus) 1) ab *
    W (replacePair (replacePair s 0 1 (.minus,.plus)) 0 1 ab))=_
  simp only [replacePair_left s (by omega : (0:ℕ)≠1),replacePair_right,replacePair_replacePair]
  rw [Finset.sum_eq_single (Spin.zero,Spin.zero)]
  · have hh : replacePair s 0 1 (Spin.zero,Spin.zero)=s := by
      simpa only [h0,h1] using replacePair_self s 0 1
    rw [hh]
  · intro ab _ hab
    rw [hW _ (by
      by_cases ha : ab.1=Spin.zero
      · right
        simp only [replacePair_right]
        intro hb
        exact hab (Prod.ext ha hb)
      · left
        simpa only [replacePair_left s (by omega : (0:ℕ)≠1)] using ha),mul_zero]
  · simp

noncomputable def zeroPairGuard : MvPolynomial ℕ ℂ :=
  polyExchangeNumerator (X 0) (X 1) (.minus,.plus) (.zero,.zero)

theorem zeroPairGuard_ne_zero : zeroPairGuard≠0 := by
  intro he
  have hh := congrArg (eval (fun i : ℕ => if i=0 then (0:ℂ) else 1)) he
  simp only [zeroPairGuard,eval_polyExchangeNumerator,eval_X,ite_true,show ¬(1:ℕ)=0 by omega,
    ite_false,map_zero] at hh
  exact offdiagonal_zero_pair_nonzero hh

theorem polynomial_zero_of_two_zero_spins
    (p : (ℕ → Spin) → MvPolynomial ℕ ℂ)
    (hz : ∀ s, s 0≠Spin.zero ∨ s 1≠Spin.zero → p s=0)
    (hex : ∀ Y, siteR 0 (Y 0) (Y 1) (fun s => eval Y (p s))=
      exchangeDenominator (Y 0) (Y 1) • (fun s => eval (swapSite 0 Y) (p s))) :
    ∀ s, p s=0 := by
  intro s
  by_cases hs : s 0≠Spin.zero ∨ s 1≠Spin.zero
  · exact hz s hs
  push Not at hs
  apply polynomial_eq_on_generic zeroPairGuard_ne_zero
  intro Y hY
  have hW : ∀ u, u 0≠Spin.zero ∨ u 1≠Spin.zero → eval Y (p u)=0 := by
    intro u hu; rw [hz u hu,map_zero]
  have he := congrFun (hex Y) (replacePair s 0 1 (.minus,.plus))
  rw [siteR_zero_pair _ _ _ s hs.1 hs.2 hW] at he
  have hZ := hz (replacePair s 0 1 (.minus,.plus)) (Or.inl (by simp))
  simp only [Pi.smul_apply,smul_eq_mul,hZ,map_zero,mul_zero] at he
  have hD : exchangeNumerator (Y 0) (Y 1) (.minus,.plus) (.zero,.zero)≠0 := by
    simpa only [zeroPairGuard,eval_polyExchangeNumerator,eval_X] using hY
  exact (mul_eq_zero.mp he).resolve_left hD

end PolynomialVacuumAlgebra

end OAI

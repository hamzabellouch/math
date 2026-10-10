import OAI.Combinatorics.PolynomialVacuum.Algebra.CupSlidePolynomial

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def polyExchangeDenominator {ι : Type*} (x y : MvPolynomial ι ℂ) :
    MvPolynomial ι ℂ := (C (t^2)*x-y)*(C T*x-y)

@[simp] theorem eval_polyExchangeDenominator {ι : Type*} (Y : ι → ℂ)
    (x y : MvPolynomial ι ℂ) : eval Y (polyExchangeDenominator x y)=
      exchangeDenominator (eval Y x) (eval Y y) := by
  simp [polyExchangeDenominator,exchangeDenominator]

noncomputable def exchangeDiscrepancy {N : ℕ} (Ψ : State N) (j : ℕ) (s : ℕ → Spin) :
    MvPolynomial ℕ ℂ :=
  (∑ ab : Pair, polyExchangeNumerator (X j) (X (j+1)) (s j,s (j+1)) ab *
    coordinatePolynomial Ψ (replacePair s j (j+1) ab))-
  polyExchangeDenominator (X j) (X (j+1))*rename (Equiv.swap j (j+1)) (coordinatePolynomial Ψ s)

@[simp] theorem eval_exchangeDiscrepancy {N : ℕ} (Ψ : State N) (j : ℕ) (s : ℕ → Spin)
    (Y : ℕ → ℂ) : eval Y (exchangeDiscrepancy Ψ j s)=
      (siteR j (Y j) (Y (j+1)) (liftState Ψ Y)) s-
        exchangeDenominator (Y j) (Y (j+1))*liftState Ψ (swapSite j Y) s := by
  simp [exchangeDiscrepancy,siteR,pairLinear,pairAction,eval_rename,swapSite]

theorem exchangeDiscrepancy_zero_iff {N : ℕ} (Ψ : State N) (j : ℕ) :
    (∀ s, exchangeDiscrepancy Ψ j s=0) ↔
      ∀ Y, siteR j (Y j) (Y (j+1)) (liftState Ψ Y)=
        exchangeDenominator (Y j) (Y (j+1)) • liftState Ψ (swapSite j Y) := by
  constructor
  · intro h Y
    funext s
    have he := congrArg (eval Y) (h s)
    simpa only [eval_exchangeDiscrepancy,map_zero,sub_eq_zero,Pi.smul_apply,smul_eq_mul] using he
  · intro h s
    apply MvPolynomial.funext
    intro Y
    simp only [map_zero,eval_exchangeDiscrepancy]
    exact sub_eq_zero.mpr (congrFun (h Y) s)

noncomputable def partialTrainGuard (n i : ℕ) : MvPolynomial ℕ ℂ :=
  ∏ j ∈ Finset.range (n-i-1), polyExchangeDenominator (C T*X i) (X (i+1+j))

end PolynomialVacuumAlgebra

end OAI

import OAI.Combinatorics.PolynomialVacuum.Algebra.CupProductSwap
import OAI.Combinatorics.PolynomialVacuum.Algebra.VectorBilinear

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

abbrev NatPolyTensor := (ℕ → Spin) → MvPolynomial ℕ ℂ
noncomputable def evalNatPolyTensor (p : NatPolyTensor) (Y : ℕ → ℂ) : SpinTensor ℕ ℂ :=
  fun s => eval Y (p s)
noncomputable def polyTensorExchange (j : ℕ) (p : NatPolyTensor) (s : ℕ → Spin) : MvPolynomial ℕ ℂ :=
  ∑ ab : Pair, polyExchangeNumerator (X j) (X (j+1)) (s j,s (j+1)) ab*p (replacePair s j (j+1) ab)
noncomputable def polyEigenOne (j : ℕ) : MvPolynomial ℕ ℂ :=
  (C T*X (j+1)-X j)*(C (t^2)*X j-X (j+1))
@[simp] theorem eval_polyTensorExchange (j : ℕ) (p : NatPolyTensor) (s : ℕ → Spin) (Y : ℕ → ℂ) :
    eval Y (polyTensorExchange j p s)=siteR j (Y j) (Y (j+1)) (evalNatPolyTensor p Y) s := by
  simp [polyTensorExchange,siteR,pairLinear,pairAction,evalNatPolyTensor]
@[simp] theorem eval_polyEigenOne (j : ℕ) (Y : ℕ → ℂ) : eval Y (polyEigenOne j)=eigenOne (Y j) (Y (j+1)) := by
  simp [polyEigenOne,eigenOne]

theorem scalar_quotient_exchange (x y H K A B : ℂ) (hH : H≠0) (hg : y-T*x≠0)
    (h : H*A=exchangeDenominator x y*K*B)
    (hQ : (y-T*x)*K=(x-T*y)*H) : A=eigenOne x y*B := by
  apply mul_left_cancel₀ (mul_ne_zero hg hH)
  unfold eigenOne
  unfold exchangeDenominator at h
  linear_combination (y-T*x)*h+((t^2*x-y)*(T*x-y)*B)*hQ

theorem cupQuotient_exchange {m j : ℕ} (hj : j+1 < m) (p r : NatPolyTensor)
    (hr : ∀ s, p s=cupVandermonde m*r s)
    (hex : ∀ Y, siteR j (Y j) (Y (j+1)) (evalNatPolyTensor p Y)=
      exchangeDenominator (Y j) (Y (j+1)) • evalNatPolyTensor p (swapSite j Y)) :
    ∀ Y, siteR j (Y j) (Y (j+1)) (evalNatPolyTensor r Y)=
      eigenOne (Y j) (Y (j+1)) • evalNatPolyTensor r (swapSite j Y) := by
  have hev (Y : ℕ → ℂ) : evalNatPolyTensor p Y=eval Y (cupVandermonde m) • evalNatPolyTensor r Y := by
    funext s; simp only [evalNatPolyTensor,hr,map_mul,Pi.smul_apply,smul_eq_mul]
  have he (s : ℕ → Spin) : polyTensorExchange j r s=
      polyEigenOne j*rename (Equiv.swap j (j+1)) (r s) := by
    apply polynomial_eq_on_generic (p:=polyTensorExchange j r s)
      (g:=cupFactor j (j+1)*cupVandermonde m)
      (mul_ne_zero (cupFactor_ne_zero (by omega)) (cupVandermonde_ne_zero m))
    intro Y hY
    have hY' : (Y (j+1)-T*Y j)*eval Y (cupVandermonde m)≠0 := by
      simpa only [map_mul,cupFactor,map_sub,eval_X,eval_C] using hY
    obtain ⟨hf,hQ⟩ := mul_ne_zero_iff.mp hY'
    have hh := hex Y
    rw [hev Y,hev (swapSite j Y),map_smul,smul_smul] at hh
    have hhs := congrFun hh s
    simp only [Pi.smul_apply,smul_eq_mul] at hhs
    have hc := scalar_quotient_exchange (Y j) (Y (j+1)) _ _ _ _ hQ hf hhs
      (eval_cupVandermonde_swap hj Y)
    simpa only [eval_polyTensorExchange,map_mul,eval_polyEigenOne,eval_rename,swapSite,
      Function.comp_def,evalNatPolyTensor] using hc
  intro Y
  funext s
  have hh := congrArg (eval Y) (he s)
  simpa only [eval_polyTensorExchange,map_mul,eval_polyEigenOne,eval_rename,swapSite,
    Function.comp_def,evalNatPolyTensor,Pi.smul_apply,smul_eq_mul] using hh

end PolynomialVacuumAlgebra

end OAI

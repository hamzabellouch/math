import OAI.Combinatorics.PolynomialVacuum.Algebra.PolynomialScalars
import OAI.Combinatorics.PolynomialVacuum.Algebra.NodeFactors

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical PolynomialVacuumInterpolation

theorem denominator_one_ne_zero : exchangeDenominator 1 1≠0 := by
  have h2 : t^2≠1 := by
    intro h
    have hh := congrArg (fun z : ℂ => z^2) h
    norm_num [t,← pow_mul,q_pow_eight] at hh
  have hT : T≠1 := by
    intro h
    have hh := congrArg (fun z : ℂ => z^4) h
    norm_num [T,t,← pow_mul,q_pow_24] at hh
  simpa only [exchangeDenominator,mul_one] using mul_ne_zero (sub_ne_zero.mpr h2) (sub_ne_zero.mpr hT)

noncomputable def genericGuard {m : ℕ} (κ : Fin m → Fin m) : MvPolynomial (Fin m) ℂ :=
  ∏ a : Fin m, ∏ b : Fin m,
    (C (t^2)*X (κ a)-X (κ b))*(C T*X (κ a)-X (κ b))

@[simp] theorem eval_genericGuard {m : ℕ} (κ : Fin m → Fin m) (Z : Fin m → ℂ) :
    eval Z (genericGuard κ)=∏ a : Fin m, ∏ b : Fin m, exchangeDenominator (Z (κ a)) (Z (κ b)) := by
  simp [genericGuard,exchangeDenominator]

theorem genericGuard_ne_zero {m : ℕ} (κ : Fin m → Fin m) : genericGuard κ≠0 := by
  intro h
  have hh := congrArg (eval (fun _ => (1:ℂ))) h
  rw [eval_genericGuard,map_zero] at hh
  have hn : (∏ a : Fin m, ∏ b : Fin m, exchangeDenominator 1 1)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact denominator_one_ne_zero
  exact hn hh

theorem polynomial_eq_on_generic {ι : Type*} {p r g : MvPolynomial ι ℂ}
    (hg : g≠0) (h : ∀ X, eval X g≠0 → eval X p=eval X r) : p=r := by
  apply mul_left_cancel₀ hg
  apply MvPolynomial.funext
  intro X
  by_cases hX : eval X g=0
  · simp [hX]
  · simp only [map_mul,h X hX]

end PolynomialVacuumAlgebra

end OAI

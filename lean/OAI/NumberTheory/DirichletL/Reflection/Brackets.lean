import OAI.NumberTheory.DirichletL.Reflection.Static
import OAI.NumberTheory.DirichletL.Descent.Hybrid

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss
open LocalReflectionBrackets CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance bracketField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance bracketFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem marked_bracket_cube (P : Ideal Eis) [P.IsMaximal]
    (hg : λ₀ ∉ P) (n b : Eis) :
    bracket (actualSextic P hg) 0 (Ideal.Quotient.mk P (n*b^3)) =
      (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)⁻¹ *
      (idealRowHom n P)⁻¹^2 * (if IsCoprime P (Ideal.span {b}) then 1 else 0) := by
  have h6 : (actualSextic P hg (Ideal.Quotient.mk P b))^6 =
      if b ∈ P then 0 else 1 := by
    simpa only [map_pow] using canonicalSextic_sixth_power_mask P hg b
  have h6' : (actualSextic P hg (Ideal.Quotient.mk P b))^6 = 0 ∨
      (actualSextic P hg (Ideal.Quotient.mk P b))^6 = 1 := by
    rw [h6]; split_ifs <;> simp
  let ψ : Eis →* ℂ := (actualSextic P hg).toMonoidHom.comp (Ideal.Quotient.mk P).toMonoidHom
  have he := InverseMoment.inverse_square_cube_mask ψ n b h6'
  change ((actualSextic P hg) (Ideal.Quotient.mk P (n*b^3)))⁻¹^2 =
    ((actualSextic P hg) (Ideal.Quotient.mk P n))⁻¹^2 *
      ((actualSextic P hg) (Ideal.Quotient.mk P b))^6 at he
  simp only [bracket,show (0:ℕ) ≠ 4 by decide,↓reduceIte,
    MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),inv_pow]
  simp only [inv_pow] at he
  rw [he,rootCard_eq_sqrt_absNorm,idealRowHom_prime n P hg,h6,
    SixthPowerAverage.prime_coprime_span_iff]
  by_cases hb : b ∈ P <;> simp [hb]

theorem marked_bracket_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (n b : Eis) :
    (∏ i, bracket (actualSextic (P i) (hg i)) 0 (Ideal.Quotient.mk (P i) (n*b^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      (idealRowHom n (∏ i, P i))⁻¹^2 *
      (if IsCoprime (∏ i, P i) (Ideal.span {b}) then 1 else 0) := by
  simp_rw [marked_bracket_cube]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  have hn : (∏ i, (Real.sqrt (Ideal.absNorm (P i) : ℝ) : ℂ)⁻¹) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ := by
    rw [map_prod,Nat.cast_prod,Real.sqrt_prod,Complex.ofReal_prod,Finset.prod_inv_distrib]
    intro i hi
    positivity
  have hc : (∏ i, (idealRowHom n (P i))⁻¹^2) = (idealRowHom n (∏ i, P i))⁻¹^2 := by
    rw [map_prod,Finset.prod_pow,Finset.prod_inv_distrib]
  have hm : (∏ i, if IsCoprime (P i) (Ideal.span {b}) then (1:ℂ) else 0) =
      if IsCoprime (∏ i, P i) (Ideal.span {b}) then 1 else 0 := by
    classical
    by_cases h : ∀ i, IsCoprime (P i) (Ideal.span {b})
    · simp [h,IsCoprime.prod_left (fun i _ => h i)]
    · obtain ⟨i,hi⟩ := not_forall.mp h
      have hp : ¬ IsCoprime (∏ i, P i) (Ideal.span {b}) := by
        intro hp
        exact hi (hp.of_isCoprime_of_dvd_left (Finset.dvd_prod_of_mem P (Finset.mem_univ i)))
      rw [ite_eq_right hp]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  rw [hn,hc,hm]

theorem marked_bracket_hybrid {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∏ i, bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) := by
  rw [marked_bracket_product,InverseMoment.inverseCubicKernel_eq_inverse_square,
    (primaryGenerator_spec b hb).1]

end
end SevenEighths.InverseReflectedPhase

end OAI

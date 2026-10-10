import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.SpherePairRadialCoefficient
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereLPolynomial

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory
open scoped ContDiff ComplexConjugate
variable {n : ℕ}

noncomputable def spherePoleCoefficientND (J : ℕ) (Λ : ℝ)
    (b : SphereAmbientND n → ℂ) (e : SphereAmbientND n) (i : PoleIndexND J) : ℂ :=
  ((Λ:ℂ)^(-(i.2:ℕ):ℤ)) *
    if i.1 then sphereLND n i.2 b e else sphereLMinusND n i.2 b (-e)

lemma norm_iteratedFDeriv_conjND {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : V → ℂ) (j : ℕ) (w : V) :
    ‖iteratedFDeriv ℝ j (fun x => conj (b x)) w‖ = ‖iteratedFDeriv ℝ j b w‖ := by
  exact Complex.conjLIE.norm_iteratedFDeriv_comp_left b w j

theorem spherePoleCoefficientND_bound (J : ℕ) (C : ℝ) (hC : 0≤C) :
    ∃ D : ℝ, 0≤D ∧ ∀ (b : SphereAmbientND n → ℂ) (e : SphereAmbientND n) (A Λ : ℝ),
      ContDiff ℝ ∞ b → ‖e‖=1 → 1≤A → 0<Λ → A^2≤Λ →
      (∀ k≤2*J, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b w‖≤C*A^k) →
      ∀ i : PoleIndexND J, ‖spherePoleCoefficientND J Λ b e i‖≤D := by
  have hex (j : Fin (J+1)) := normalizedDifferentialND_bound (sphereBasisND n)
    (sphereLPolynomialND n j) j (stationaryLPolynomialND_degree _ _ _) C hC
  choose D hD hDb using hex
  refine ⟨∑ j : Fin (J+1), D j, Finset.sum_nonneg (fun j _ => hD j), ?_⟩
  intro b e A Λ hb he hA hΛ hscale hder i
  have hder' : ∀ k≤2*(i.2:ℕ), ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ k b w‖≤C*A^k := by
    intro k hk w hw
    exact hder k (by have := i.2.isLt; omega) w hw
  have hpay : ((Λ:ℂ)^(-(i.2:ℕ):ℤ))=(((Λ⁻¹:ℝ):ℂ)^(i.2:ℕ)) := by
    simp [zpow_neg,zpow_natCast, inv_pow]
  have hh : ‖spherePoleCoefficientND J Λ b e i‖≤D i.2 := by
    cases hi : i.1
    · have hstar : ContDiff ℝ ∞ (fun w => conj (b w)) := by
        simpa only [Function.comp_def,Complex.conjCLE_apply] using Complex.conjCLE.contDiff.comp hb
      have h := hDb i.2 ⟨fun w => conj (b w),hstar⟩ A Λ hA hΛ hscale (by
        intro k hk w hw
        rw [norm_iteratedFDeriv_conjND]
        exact hder' k hk w hw) (-e) (by simpa using he)
      simp only [spherePoleCoefficientND,hi,Bool.false_eq_true,ite_false,sphereLMinusND,hpay]
      rw [norm_mul,norm_star]
      simpa only [normalizedDifferentialND, ← sphereLND_eq_polynomial,norm_mul,Complex.star_def] using h
    · have h := hDb i.2 ⟨b,hb⟩ A Λ hA hΛ hscale hder' e he
      simpa only [spherePoleCoefficientND,hi,ite_true,hpay,normalizedDifferentialND,
        ← sphereLND_eq_polynomial] using h
  exact hh.trans (Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ _))

lemma radialPoleSumND_coefficients (J : ℕ) (Λ u : ℝ) (hΛ : 0<Λ) (hu : 0<u)
    (b : SphereAmbientND n → ℂ) (e : SphereAmbientND n) :
    radialPoleSumND n J Λ (spherePoleCoefficientND J Λ b e) u =
      (((Λ*u)^(-(n:ℝ)/2):ℝ):ℂ) *
        (Complex.exp (Complex.I*((Λ*u):ℝ)) *
          ∑ j∈Finset.range (J+1), ((Λ*u:ℝ):ℂ)^(-(j:ℤ))*sphereLND n j b e +
        Complex.exp (-(Complex.I*((Λ*u):ℝ))) *
          ∑ j∈Finset.range (J+1), ((Λ*u:ℝ):ℂ)^(-(j:ℤ))*sphereLMinusND n j b (-e)) := by
  have hp (j : ℕ) : (((Λ^(-(n:ℝ)/2):ℝ):ℂ)*((Λ:ℂ)^(-(j:ℤ))))*
      ((u^(-(n:ℝ)/2-j):ℝ):ℂ) =
      (((Λ*u)^(-(n:ℝ)/2):ℝ):ℂ)*((Λ*u:ℝ):ℂ)^(-(j:ℤ)) := by
    rw [Real.mul_rpow hΛ.le hu.le,Complex.ofReal_mul,Complex.ofReal_mul,mul_zpow,
      Real.rpow_sub hu,Real.rpow_natCast,Complex.ofReal_div,Complex.ofReal_pow]
    simp only [zpow_neg,zpow_natCast]
    ring
  rw [radialPoleSumND,Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [spherePoleCoefficientND,poleSignND,Bool.false_eq_true,ite_true,ite_false,
    Complex.ofReal_one,Complex.ofReal_neg,one_mul,neg_one_mul]
  simp only [mul_add]
  congr 1 <;>
    rw [← Fin.sum_univ_eq_sum_range] <;>
    simp only [Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro j hj
  · calc
      _ = ((((Λ^(-(n:ℝ)/2):ℝ):ℂ)*((Λ:ℂ)^(-((j:ℕ):ℤ))))*
        ((u^(-(n:ℝ)/2-(j:ℕ)):ℝ):ℂ)) * Complex.exp (Complex.I*(Λ:ℂ)*(u:ℂ))*sphereLND n j b e := by ring
      _ = _ := by rw [hp]; push_cast; simp only [mul_assoc]; ring
  · calc
      _ = ((((Λ^(-(n:ℝ)/2):ℝ):ℂ)*((Λ:ℂ)^(-((j:ℕ):ℤ))))*
        ((u^(-(n:ℝ)/2-(j:ℕ)):ℝ):ℂ)) * Complex.exp (-(Complex.I*(Λ:ℂ)*(u:ℂ)))*sphereLMinusND n j b (-e) := by
          ring_nf
      _ = _ := by rw [hp]; push_cast; simp only [mul_assoc]; ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI

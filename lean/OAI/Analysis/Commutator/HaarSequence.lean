import Mathlib

namespace OAI

noncomputable section

noncomputable section

open scoped InnerProductSpace ComplexOrder

open UniformSpace Filter Topology

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma orthonormal_inner_tendsto_zero (v : ℕ → H) (hv : Orthonormal ℂ v) (y : H) :
    Tendsto (fun n => inner ℂ (v n) y) atTop (𝓝 0) := by
  have hs := (hv.inner_products_summable (x := y)).tendsto_atTop_zero
  have hn : Tendsto (fun n => ‖inner ℂ (v n) y‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : τ 1=1) (z : unitary A)

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitary_pow_gram_of_le {n m : ℕ} (hnm : n ≤ m) :
    star ((z : A)^n)*(z : A)^m=(z : A)^(m-n) := by
  have hm : m=n+(m-n) := by omega
  rw [hm, pow_add, ←mul_assoc]
  have hz : star ((z : A)^n)*(z : A)^n=1 := by
    simpa only [SubmonoidClass.coe_pow] using Unitary.coe_star_mul_self (z^n)
  rw [hz, one_mul]
  congr 1
  omega

include hτ in
lemma haar_pow_gram (hH : ∀ n : ℕ, 0<n → τ ((z : A)^n)=0) (n m : ℕ) :
    τ (star ((z : A)^n)*(z : A)^m)=if n=m then 1 else 0 := by
  rcases lt_trichotomy n m with h | h | h
  · rw [unitary_pow_gram_of_le z h.le, hH (m-n) (by omega), ite_eq_right (ne_of_lt h)]
  · subst m
    rw [unitary_pow_gram_of_le z le_rfl, Nat.sub_self, pow_zero, hτ, ite_eq_left rfl]
  · have hh : τ (star ((z : A)^m)*(z : A)^n)=0 := by
      rw [unitary_pow_gram_of_le z h.le, hH (n-m) (by omega)]
    have hs := congrArg star hh
    rw [←map_star, star_mul, star_star, star_zero] at hs
    simpa only [ite_eq_right (ne_of_gt h)] using hs

include hτ in
lemma haar_powers_orthonormal (hH : ∀ n : ℕ, 0<n → τ ((z : A)^n)=0) :
    Orthonormal ℂ (fun n : ℕ => (τ.toPreGNS ((z : A)^n) : τ.GNS)) := by
  rw [orthonormal_iff_ite]
  intro n m
  rw [Completion.inner_coe]
  exact haar_pow_gram τ hτ z hH n m

include hτ in
lemma haar_moments_tendsto_zero (hH : ∀ n : ℕ, 0<n → τ ((z : A)^n)=0) (a : A) :
    Tendsto (fun n => τ (star ((z : A)^n)*a)) atTop (𝓝 0) := by
  have h := orthonormal_inner_tendsto_zero _ (haar_powers_orthonormal τ hτ z hH)
    (τ.toPreGNS a : τ.GNS)
  simpa only [Completion.inner_coe, PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS] using h

lemma inverse_haar_moments (hH : ∀ n : ℕ, 0<n → τ ((z : A)^n)=0)
    (n : ℕ) (hn : 0<n) : τ (((z⁻¹ : unitary A) : A)^n)=0 := by
  have hz : (((z⁻¹ : unitary A) : A)^n) = star ((z : A)^n) := by
    rw [star_pow]
    rfl
  rw [hz, map_star, hH n hn, star_zero]

include hτ in
lemma haar_plain_moments_tendsto_zero
    (hH : ∀ n : ℕ, 0<n → τ ((z : A)^n)=0) (a : A) :
    Tendsto (fun n => τ ((z : A)^n*a)) atTop (𝓝 0) := by
  have h := haar_moments_tendsto_zero τ hτ z⁻¹ (inverse_haar_moments τ z hH) a
  have hz (n : ℕ) : star (((z⁻¹ : unitary A) : A)^n)=(z : A)^n := by
    rw [star_pow]
    congr 1
    exact star_star (z : A)
  simpa only [hz] using h

end Kadison
end
end

end OAI

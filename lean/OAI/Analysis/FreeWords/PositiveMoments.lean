import Mathlib
import OAI.Analysis.FreeWords.DirichletMoments

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder BigOperators

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKFreeWords

namespace KKFreeWords

open scoped BigOperators

noncomputable section

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder BigOperators

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder BigOperators

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ}

omit [StarOrderedRing A] in
theorem positiveMap_re_nonneg {x : A} (hx : 0 ≤ x) : 0 ≤ (τ x).re :=
  (Complex.nonneg_iff.mp (τ.map_nonneg hx)).1

omit [StarOrderedRing A] in
theorem positiveMap_norm_of_nonneg {x : A} (hx : 0 ≤ x) : ‖τ x‖ = (τ x).re := by
  have h := Complex.nonneg_iff.mp (τ.map_nonneg hx)
  have he : τ x = ((τ x).re : ℂ) := by apply Complex.ext <;> simp [h.2.symm]
  rw [he,Complex.norm_of_nonneg h.1]
  simp

theorem positiveMap_cauchy_schwarz (x y : A) :
    ‖τ (star x*y)‖^2 ≤ (τ (star x*x)).re * (τ (star y*y)).re := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_inner_le_norm (𝕜 := ℂ) (τ.toPreGNS x) (τ.toPreGNS y)) 2
  rw [mul_pow,← inner_self_eq_norm_sq (𝕜 := ℂ) (τ.toPreGNS x),
    ← inner_self_eq_norm_sq (𝕜 := ℂ) (τ.toPreGNS y)] at h
  simpa only [PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS, RCLike.re_eq_complex_re] using h

theorem positiveMap_moment_interpolation {x : A} (hx : 0 ≤ x) :
    (τ (x^2)).re^3 ≤ (τ x).re^2 * (τ (x^4)).re := by
  let s := CFC.sqrt x
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg x
  have hss : star s = s := (IsSelfAdjoint.of_nonneg hs0).star_eq
  have hs2 : s^2 = x := by simpa only [s,pow_two] using CFC.sqrt_mul_sqrt_self x hx
  have hxs : star x = x := (IsSelfAdjoint.of_nonneg hx).star_eq
  have h2 (n : ℕ) : s^(2*n) = x^n := by rw [pow_mul,hs2]
  have h12 := positiveMap_cauchy_schwarz (τ := τ) s (s^3)
  have hs13 : star s * s^3 = x^2 := by rw [hss,← pow_succ']; exact h2 2
  have hs33 : star (s^3)*s^3 = x^3 := by rw [star_pow,hss,← pow_add]; exact h2 3
  rw [hs13,hs33,hss,← pow_two,hs2,
    positiveMap_norm_of_nonneg (τ := τ) (CStarAlgebra.pow_nonneg x 2 hx)] at h12
  have h23 := positiveMap_cauchy_schwarz (τ := τ) x (x^2)
  have hx12 : star x*x^2 = x^3 := by rw [hxs,← pow_succ']
  have hx22 : star (x^2)*x^2 = x^4 := by rw [star_pow,hxs,← pow_add]
  rw [hx12,hx22,hxs,← pow_two,
    positiveMap_norm_of_nonneg (τ := τ) (CStarAlgebra.pow_nonneg x 3 hx)] at h23
  have hm1 := positiveMap_re_nonneg (τ := τ) hx
  have hm2 := positiveMap_re_nonneg (τ := τ) (CStarAlgebra.pow_nonneg x 2 hx)
  have hm3 := positiveMap_re_nonneg (τ := τ) (CStarAlgebra.pow_nonneg x 3 hx)
  have hm4 := positiveMap_re_nonneg (τ := τ) (CStarAlgebra.pow_nonneg x 4 hx)
  have h12s := pow_le_pow_left₀ (sq_nonneg (τ (x^2)).re) h12 2
  have h23m := mul_le_mul_of_nonneg_left h23 (sq_nonneg (τ x).re)
  by_cases hm2z : (τ (x^2)).re = 0
  · simp [hm2z,mul_nonneg (sq_nonneg (τ x).re) hm4]
  · have hm2p : 0 < (τ (x^2)).re := lt_of_le_of_ne hm2 (Ne.symm hm2z)
    have hcancel : (τ (x^2)).re * (τ (x^2)).re^3 ≤
        (τ (x^2)).re * ((τ x).re^2 * (τ (x^4)).re) := by nlinarith
    exact (mul_le_mul_iff_right₀ hm2p).mp hcancel

theorem positiveMap_fourth_le (a : A) :
    (τ ((a*star a)^2)).re ≤ ‖a‖^2 * (τ (a*star a)).re := by
  have ho := star_right_conjugate_le_conjugate
    (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := a)) a
  have he : a * (star a*a) * star a = (a*star a)^2 := by noncomm_ring
  have he' : a * (algebraMap ℝ A (‖a‖^2)) * star a = ‖a‖^2 • (a*star a) := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [mul_smul_comm,mul_one,smul_mul_assoc]
  rw [he,he'] at ho
  have h := (Complex.le_def.mp (τ.monotone' ho)).1
  change (τ ((a*star a)^2)).re ≤ (τ (‖a‖^2 • (a*star a))).re at h
  simpa only [positiveMap_real_smul,Complex.smul_re,smul_eq_mul] using h

end

end KKFreeWords
end

end OAI

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

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder BigOperators

noncomputable section

theorem real_regularization_lower {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x - 1/10 ≤ x * (Real.sqrt (x+1/100))⁻¹ := by
  have ha := Real.sqrt_nonneg x
  have hb := Real.sqrt_nonneg (x+1/100)
  have ha2 := Real.sq_sqrt hx
  have hb2 := Real.sq_sqrt (by linarith : 0 ≤ x+1/100)
  have hbp : 0 < Real.sqrt (x+1/100) := Real.sqrt_pos.mpr (by linarith)
  have hab : Real.sqrt (x+1/100) ≤ Real.sqrt x + 1/10 := by nlinarith
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hbp).mpr
  by_cases h : Real.sqrt x ≤ 1/10
  · have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hb
    linarith
  · have hm := mul_le_mul_of_nonneg_left hab (by linarith : 0 ≤ Real.sqrt x-1/10)
    nlinarith

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ}

theorem regularizer_continuous {x : A} (hx : 0 ≤ x) :
    ContinuousOn (fun t : ℝ => (Real.sqrt (t+1/100))⁻¹) (spectrum ℝ x) := by
  apply ContinuousOn.inv₀ ((continuous_id.add continuous_const).sqrt.continuousOn)
  intro t ht
  apply ne_of_gt
  apply Real.sqrt_pos.mpr
  have := spectrum_nonneg_of_nonneg hx ht
  change 0 < t + 1/100
  linarith

theorem regularized_order_lower {x : A} (hx : 0 ≤ x) :
    CFC.sqrt x - (1/10:ℝ) • (1:A) ≤
      x*cfc (fun t : ℝ => (Real.sqrt (t+1/100))⁻¹) x := by
  have hxs : IsSelfAdjoint x := IsSelfAdjoint.of_nonneg hx
  have hr := regularizer_continuous hx
  have h := (cfc_le_iff (fun t : ℝ => Real.sqrt t-1/10)
    (fun t : ℝ => t * (Real.sqrt (t+1/100))⁻¹) x
    ((Real.continuous_sqrt.sub continuous_const).continuousOn)
    (continuousOn_id.mul hr) hxs).mpr (fun t ht =>
      real_regularization_lower (spectrum_nonneg_of_nonneg hx ht))
  rw [cfc_sub Real.sqrt (fun _ : ℝ => 1/10),cfc_const (1/10:ℝ) x hxs,
    cfc_mul (fun t : ℝ => t) (fun t : ℝ => (Real.sqrt (t+1/100))⁻¹) x continuousOn_id hr,
    cfc_id' ℝ x hxs,Algebra.algebraMap_eq_smul_one] at h
  rw [CFC.sqrt_eq_real_sqrt x hx,cfcₙ_eq_cfc]
  exact h

theorem regularized_state_lower (hτ : τ 1 = 1) {x : A} (hx : 0 ≤ x) :
    (τ (CFC.sqrt x)).re - 1/10 ≤
      (τ (x*cfc (fun t : ℝ => (Real.sqrt (t+1/100))⁻¹) x)).re := by
  have h := (Complex.le_def.mp (τ.monotone' (regularized_order_lower hx))).1
  change (τ (CFC.sqrt x-(1/10:ℝ) • (1:A))).re ≤
    (τ (x*cfc (fun t : ℝ => (Real.sqrt (t+1/100))⁻¹) x)).re at h
  simpa only [map_sub,positiveMap_real_smul,hτ,Complex.sub_re,Complex.smul_re,
    Complex.one_re,smul_eq_mul,mul_one] using h

end

end KKFreeWords
end

end OAI

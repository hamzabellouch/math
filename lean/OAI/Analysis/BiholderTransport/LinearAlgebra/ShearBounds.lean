import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.ShearConvexity

namespace OAI

section
section
noncomputable section
open Set ContinuousLinearMap

namespace WeakMTWTransport
section ShearBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma rankOne_perturbation_bounds (q : E) {r U : ℝ}
    (hlo : -(1/2:ℝ) ≤ r*‖q‖^2) (hup : |r| *‖q‖^2 ≤ U) (v : E) :
    (1/2:ℝ)*‖v‖ ≤ ‖v+(r*inner ℝ v q) • q‖ ∧
    ‖v+(r*inner ℝ v q) • q‖ ≤ (1+U)*‖v‖ := by
  have hcs : |inner ℝ v q| ≤ ‖v‖*‖q‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) v q
  have hcs2 : (inner ℝ v q)^2 ≤ ‖q‖^2*‖v‖^2 := by
    have H := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hcs
    simpa only [sq_abs,mul_pow,mul_comm] using H
  have hinner : inner ℝ (v+(r*inner ℝ v q) • q) v=
      ‖v‖^2+r*(inner ℝ v q)^2 := by
    rw [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,real_inner_comm q v]
    ring
  have hcoer : (1/2:ℝ)*‖v‖^2 ≤ inner ℝ (v+(r*inner ℝ v q) • q) v := by
    rw [hinner]
    by_cases hr : 0 ≤ r
    · nlinarith [mul_nonneg hr (sq_nonneg (inner ℝ v q))]
    · have H := mul_le_mul_of_nonpos_left hcs2 (le_of_not_ge hr)
      have H2 := mul_le_mul_of_nonneg_right hlo (sq_nonneg ‖v‖)
      nlinarith only [H,H2]
  constructor
  · by_cases hv : v=0
    · simp [hv]
    · have H := hcoer.trans (real_inner_le_norm _ _)
      have hn : 0<‖v‖ := norm_pos_iff.mpr hv
      nlinarith only [H,hn]
  · calc
      _ ≤ ‖v‖+‖(r*inner ℝ v q) • q‖ := norm_add_le _ _
      _ = ‖v‖+|r| *|inner ℝ v q| *‖q‖ := by rw [norm_smul,Real.norm_eq_abs,abs_mul]
      _ ≤ ‖v‖+|r| *(‖v‖*‖q‖)*‖q‖ := by gcongr
      _ = ‖v‖+(|r| *‖q‖^2)*‖v‖ := by ring
      _ ≤ ‖v‖+U*‖v‖ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hup (norm_nonneg v))
      _ = _ := by ring

lemma spectralShear_uniform_bounds (p q : E) {a B t : ℝ}
    (ha : 0<a) (hB : 0<B) (haB : a*B ≤ 1/2)
    (hpq : 0< inner ℝ p q) (hβ : ‖q‖^2/inner ℝ p q ≤ B)
    (ht : t∈Icc (-a) 1) (v : E) :
    (1/2:ℝ)*‖v‖ ≤ ‖spectralShear p q t v‖ ∧
    ‖spectralShear p q t v‖ ≤ (2+B)*‖v‖ := by
  let β := ‖q‖^2/inner ℝ p q
  have hβ0 : 0 ≤ β := div_nonneg (sq_nonneg _) hpq.le
  have htlo : -(1/2:ℝ) ≤ t*β := by
    have H := mul_le_mul_of_nonneg_right ht.1 hβ0
    have H2 := mul_le_mul_of_nonneg_left hβ ha.le
    change a*β ≤ a*B at H2
    nlinarith only [H,H2,haB]
  have htu : |t| *β ≤ 1+B := by
    have hupper := mul_le_mul_of_nonneg_right ht.2 hβ0
    change β ≤ B at hβ
    calc
      |t| *β = |t*β| := by rw [abs_mul,abs_of_nonneg hβ0]
      _ ≤ 1+B := abs_le.mpr
        ⟨by linarith only [htlo,hB],by linarith only [hupper,hβ]⟩
  have hlo : -(1/2:ℝ) ≤ (t/inner ℝ p q)*‖q‖^2 := by
    simpa only [β,div_mul_eq_mul_div,mul_div_assoc,mul_comm t] using htlo
  have hup : |t/inner ℝ p q| *‖q‖^2 ≤ 1+B := by
    rw [abs_div,abs_of_pos hpq]
    simpa only [β,div_mul_eq_mul_div,mul_div_assoc] using htu
  have H := rankOne_perturbation_bounds q hlo hup v
  rw [spectralShear_apply]
  have he : t*(inner ℝ v q/inner ℝ p q)=(t/inner ℝ p q)*inner ℝ v q := by ring
  rw [he]
  simpa only [show (1:ℝ)+(1+B)=2+B by ring] using H

lemma spectralShear_bijective [FiniteDimensional ℝ E] (p q : E) {a B t : ℝ}
    (ha : 0<a) (hB : 0<B) (haB : a*B ≤ 1/2)
    (hpq : 0< inner ℝ p q) (hβ : ‖q‖^2/inner ℝ p q ≤ B) (ht : t∈Icc (-a) 1) :
    Function.Bijective (spectralShear p q t) := by
  have hinj : Function.Injective (spectralShear p q t) := by
    change Function.Injective (spectralShear p q t).toLinearMap
    rw [← LinearMap.ker_eq_bot (f := (spectralShear p q t).toLinearMap),LinearMap.ker_eq_bot']
    intro v hv
    have H := (spectralShear_uniform_bounds p q ha hB haB hpq hβ ht v).1
    change spectralShear p q t v=0 at hv
    rw [hv,norm_zero] at H
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  exact ⟨hinj,(LinearMap.injective_iff_surjective (f := (spectralShear p q t).toLinearMap)).mp hinj⟩
end ShearBounds
end WeakMTWTransport

end

end

end

end OAI

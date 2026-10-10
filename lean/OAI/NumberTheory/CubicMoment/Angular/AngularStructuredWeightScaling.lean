import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeMomentCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.StructuredWeightScaling

namespace OAI

/-! Exact scaling identities for fixed-angular structured prime coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

lemma structuredAngularPrimeMoment_mul_weights (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0)
    (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    structuredAngularPrimeMoment ℓ a b v e u (fun i x => c i*W i x) X V Y =
      (∏ i, c i)*structuredAngularPrimeMoment ℓ a b v e u W X V Y := by
  unfold structuredAngularPrimeMoment primeMomentCoefficient
  rw [coordinatePrimeSupport_mul_weights W c hc]
  simp_rw [squarefreeConvolution_mul_weights]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

lemma structuredAngularPrimeMoment_log_scaling (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) (s : ℝ) :
    structuredAngularPrimeMoment ℓ a b v e u W X V Y =
      ((Y^(s*(Fintype.card ι:ℝ)):ℝ):ℂ)*
        structuredAngularPrimeMoment ℓ a b v e u (fun i x => ((Y^(-s):ℝ):ℂ)*W i x) X V Y := by
  have hw : (fun i x => ((Y^s:ℝ):ℂ)*(((Y^(-s):ℝ):ℂ)*W i x)) = W := by
    funext i x
    rw [← mul_assoc,← Complex.ofReal_mul,← Real.rpow_add hY]
    simp
  have h := structuredAngularPrimeMoment_mul_weights ℓ a b v e u
    (fun i x => ((Y^(-s):ℝ):ℂ)*W i x) (fun _ => ((Y^s:ℝ):ℂ))
    (fun _ => Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hY s).ne') X V Y
  rw [hw] at h
  simpa only [Finset.prod_const,Finset.card_univ,← Complex.ofReal_pow,
    ← Real.rpow_natCast,← Real.rpow_mul hY.le] using h

lemma structuredAngularPrimeMoment_log_scaling_base (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Z : ℝ) {Y : ℝ} (hY : 0 < Y) (s : ℝ) :
    structuredAngularPrimeMoment ℓ a b v e u W X V Z =
      ((Y^(s*(Fintype.card ι:ℝ)):ℝ):ℂ)*
        structuredAngularPrimeMoment ℓ a b v e u (fun i x => ((Y^(-s):ℝ):ℂ)*W i x) X V Z := by
  have hw : (fun i x => ((Y^s:ℝ):ℂ)*(((Y^(-s):ℝ):ℂ)*W i x)) = W := by
    funext i x
    rw [← mul_assoc,← Complex.ofReal_mul,← Real.rpow_add hY]
    simp
  have h := structuredAngularPrimeMoment_mul_weights ℓ a b v e u
    (fun i x => ((Y^(-s):ℝ):ℂ)*W i x) (fun _ => ((Y^s:ℝ):ℂ))
    (fun _ => Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hY s).ne') X V Z
  rw [hw] at h
  simpa only [Finset.prod_const,Finset.card_univ,← Complex.ofReal_pow,
    ← Real.rpow_natCast,← Real.rpow_mul hY.le] using h

end CubicFirstMoment

end

end OAI

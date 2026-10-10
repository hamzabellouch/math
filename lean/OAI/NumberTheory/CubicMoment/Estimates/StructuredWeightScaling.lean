import OAI.NumberTheory.CubicMoment.Estimates.PrimeMomentCoefficient
import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily

namespace OAI

/-! Exact scaling of the original structured prime weights. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_mul_weights (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (c : ι → ℂ) (z : Eisenstein) :
    orderedConvolution S (fun i n => c i*w i n) z =
      (∏ i, c i)*orderedConvolution S w z := by
  unfold orderedConvolution
  simp_rw [Finset.prod_mul_distrib]
  rw [Finset.mul_sum]

lemma squarefreeConvolution_mul_weights (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (c : ι → ℂ) (z : Eisenstein) :
    squarefreeConvolution S (fun i n => c i*w i n) z =
      (∏ i, c i)*squarefreeConvolution S w z := by
  by_cases hz : Squarefree z
  · simp only [squarefreeConvolution,ite_eq_left hz,orderedConvolution_mul_weights]
  · simp only [squarefreeConvolution,ite_eq_right hz,mul_zero]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinatePrimeSupport_mul_weights (W : ι → ℝ → ℂ) (c : ι → ℂ)
    (hc : ∀ i, c i ≠ 0) (X : ι → ℝ) (Y : ℝ) :
    coordinatePrimeSupport (fun i x => c i*W i x) X Y = coordinatePrimeSupport W X Y := by
  funext i
  ext n
  simp only [coordinatePrimeSupport,coordinateSupport,Finset.mem_filter,mul_ne_zero_iff]
  tauto

lemma structuredPrimeMoment_mul_weights (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0)
    (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    structuredPrimeMoment a b v e u (fun i x => c i*W i x) X V Y =
      (∏ i, c i)*structuredPrimeMoment a b v e u W X V Y := by
  unfold structuredPrimeMoment primeMomentCoefficient
  rw [coordinatePrimeSupport_mul_weights W c hc]
  simp_rw [squarefreeConvolution_mul_weights]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

lemma structuredPrimeMoment_log_scaling (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) (s : ℝ) :
    structuredPrimeMoment a b v e u W X V Y =
      ((Y^(s*(Fintype.card ι:ℝ)):ℝ):ℂ)*
        structuredPrimeMoment a b v e u (fun i x => ((Y^(-s):ℝ):ℂ)*W i x) X V Y := by
  have hw : (fun i x => ((Y^s:ℝ):ℂ)*(((Y^(-s):ℝ):ℂ)*W i x)) = W := by
    funext i x
    rw [← mul_assoc,← Complex.ofReal_mul,← Real.rpow_add hY]
    simp
  have h := structuredPrimeMoment_mul_weights a b v e u
    (fun i x => ((Y^(-s):ℝ):ℂ)*W i x) (fun _ => ((Y^s:ℝ):ℂ))
    (fun _ => Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hY s).ne') X V Y
  rw [hw] at h
  simpa only [Finset.prod_const,Finset.card_univ,← Complex.ofReal_pow,
    ← Real.rpow_natCast,← Real.rpow_mul hY.le] using h

lemma structuredPrimeMoment_log_scaling_base (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Z : ℝ) {Y : ℝ} (hY : 0 < Y) (s : ℝ) :
    structuredPrimeMoment a b v e u W X V Z =
      ((Y^(s*(Fintype.card ι:ℝ)):ℝ):ℂ)*
        structuredPrimeMoment a b v e u (fun i x => ((Y^(-s):ℝ):ℂ)*W i x) X V Z := by
  have hw : (fun i x => ((Y^s:ℝ):ℂ)*(((Y^(-s):ℝ):ℂ)*W i x)) = W := by
    funext i x
    rw [← mul_assoc,← Complex.ofReal_mul,← Real.rpow_add hY]
    simp
  have h := structuredPrimeMoment_mul_weights a b v e u
    (fun i x => ((Y^(-s):ℝ):ℂ)*W i x) (fun _ => ((Y^s:ℝ):ℂ))
    (fun _ => Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hY s).ne') X V Z
  rw [hw] at h
  simpa only [Finset.prod_const,Finset.card_univ,← Complex.ofReal_pow,
    ← Real.rpow_natCast,← Real.rpow_mul hY.le] using h

lemma normalized_energy_transfer {α : Type*} (S : Finset α)
    (f g : α → ℂ) {Y e d : ℝ} (hY : 1 ≤ Y)
    (hscale : ∀ i ∈ S, f i = ((Y^d:ℝ):ℂ)*g i)
    (hbound : (∑ i ∈ S, ‖g i‖^2) ≤ Y^(7/3-e)) (hd : 2*d ≤ e/2) :
    (∑ i ∈ S, ‖f i‖^2) ≤ Y^(7/3-e/2) := by
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  calc
    _ = Y^(2*d)*(∑ i ∈ S, ‖g i‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hscale i hi,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hYp.le _),mul_pow,
        ← Real.rpow_natCast,← Real.rpow_mul hYp.le]
      congr 2
      ring
    _ ≤ Y^(2*d)*Y^(7/3-e) := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hYp.le _)
    _ = Y^(2*d+(7/3-e)) := (Real.rpow_add hYp _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY (by linarith)

end CubicFirstMoment

end

end OAI

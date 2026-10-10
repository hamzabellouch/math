import OAI.Analysis.IrrationalRotation.Spectral.ProductFinitePolar
import OAI.Analysis.IrrationalRotation.Spectral.PolarFactor

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

theorem realMultiplier_nonneg
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hpos : ∀ x, 0 ≤ f x) :
    0 ≤ multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb := by
  have hsqrtb : ∀ x, ‖(Real.sqrt (f x) : ℂ)‖ ≤ Real.sqrt C := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos x)] using hb x
  let R := multiplier θ (fun x => (Real.sqrt (f x) : ℂ)) (Real.sqrt C)
    (Real.sqrt_nonneg C) hf.sqrt.complex_ofReal hsqrtb
  let B := multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb
  have hR : IsSelfAdjoint R := by
    apply isSelfAdjoint_of_real_sequence_diagonal
      (fun k x => Real.sqrt (f (rotationIterate θ k x))) R
    intro v k
    exact (multiplier_coordinate_ae θ _ _ _ _ hsqrtb v).mono (fun x hx => hx k)
  have hRR : R * R = B := by
    apply ContinuousLinearMap.ext
    intro v
    apply Lp.ext
    filter_upwards [multiplier_coordinate_ae θ _ _ _ _ hsqrtb (R v),
      multiplier_coordinate_ae θ _ _ _ _ hsqrtb v,
      multiplier_coordinate_ae θ _ C hC hf.complex_ofReal hb v]
      with x houter hinner hB
    apply lp.ext
    funext k
    change R (R v) x k = B v x k
    rw [houter, hinner, hB, ← mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hpos _)]
  change 0 ≤ B
  rw [← hRR]
  simpa only [hR.star_eq] using star_mul_self_nonneg R

theorem operatorModulus_shift_mul_realMultiplier
    (θ : ℕ → ℝ) (f : Base → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : Measurable f) (hb : ∀ x, ‖(f x : ℂ)‖ ≤ C)
    (hpos : ∀ x, 0 ≤ f x) :
    operatorModulus
      (shiftOperator * multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb) =
      multiplier θ (fun x => (f x : ℂ)) C hC hf.complex_ofReal hb := by
  let U : unitary (Hilbert →L[ℂ] Hilbert) :=
    ⟨shiftOperator, WeightedShift.fieldShift_mem_unitary (μ := baseMeasure) 1⟩
  exact PolarFactor.abs_unitary_mul_of_nonneg U _ (realMultiplier_nonneg θ f C hC hf hb hpos)

end Invariant233.ProductModel

end

end OAI

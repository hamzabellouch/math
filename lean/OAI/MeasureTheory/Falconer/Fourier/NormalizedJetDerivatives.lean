import OAI.MeasureTheory.Falconer.Fourier.JetDerivativeBounds

namespace OAI

/-! # Scale-normalized ambient derivatives of a single mask -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

noncomputable def normalizedAmbientDescriptorJet {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PlanarFalconer.PolicyDescriptor) (S : Finset (Sphere d))
    (k : ℕ) (v : Fin k → Space d) (x z : Space d) : ℝ :=
  (descriptorMaskRadius N σ b)^k *
    (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) z) v

 theorem normalizedAmbientDescriptorJet_sphere {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PlanarFalconer.PolicyDescriptor) (S : Finset (Sphere d))
    (k : ℕ) (v : Fin k → Space d) (x : Space d) (w : Sphere d) :
    (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x w : ℂ) =
      normalizedDescriptorJet Q ρ m N σ J i b S k v x w := rfl

 theorem normalizedAmbientDescriptorJet_contDiff {d : ℕ} (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (b : PlanarFalconer.PolicyDescriptor) (S : Finset (Sphere d))
    (k : ℕ) (v : Fin k → Space d) (x : Space d) :
    ContDiff ℝ ∞ (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x) := by
  exact contDiff_const.mul
    ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Space d) ℝ v).contDiff.comp
      ((descriptorAmbientMask_contDiff Q ρ m N σ J i b S x).iteratedFDeriv_right (by simp)))

 theorem normalizedAmbientDescriptorJet_derivatives (d k t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q : DyadicCube d) (ρ : Measure (Space d))
      (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ) (b : PlanarFalconer.PolicyDescriptor)
      (S : Finset (Sphere d)),
      (∀ w ∈ S, ∀ z ∈ S, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ (v : Fin k → Space d), (∀ j, ‖v j‖ ≤ 1) →
      ∀ (x z : Space d),
        ‖iteratedFDeriv ℝ t (normalizedAmbientDescriptorJet Q ρ m N σ J i b S k v x) z‖ ≤
          C * ((descriptorMaskRadius N σ b)⁻¹)^t := by
  obtain ⟨C,hC,hbound⟩ := descriptorJetValue_derivatives d k t
  refine ⟨C,hC,?_⟩
  intro Q ρ m N σ J i b S hsep v hv x z
  have hr := descriptorMaskRadius_pos N σ b
  have hf : ContDiff ℝ ∞ (fun y =>
      (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) y) v) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Space d) ℝ v).contDiff.comp
      ((descriptorAmbientMask_contDiff Q ρ m N σ J i b S x).iteratedFDeriv_right (by simp))
  change ‖iteratedFDeriv ℝ t (fun y => (descriptorMaskRadius N σ b)^k •
    (iteratedFDeriv ℝ k (descriptorAmbientMask Q ρ m N σ J i b S x) y) v) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hf.of_le (by simp)).contDiffAt,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr.le k)]
  calc
    _ ≤ (descriptorMaskRadius N σ b)^k * (C*((descriptorMaskRadius N σ b)⁻¹)^(k+t)) :=
      mul_le_mul_of_nonneg_left (hbound Q ρ m N σ J i b S hsep v hv x z) (pow_nonneg hr.le k)
    _ = C*((descriptorMaskRadius N σ b)⁻¹)^t := by
      rw [pow_add]
      calc
        _ = ((descriptorMaskRadius N σ b)*(descriptorMaskRadius N σ b)⁻¹)^k *
            (C*((descriptorMaskRadius N σ b)⁻¹)^t) := by rw [mul_pow]; ring
        _ = _ := by rw [mul_inv_cancel₀ hr.ne',one_pow,one_mul]

end Falconer

end OAI

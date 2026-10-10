import OAI.MeasureTheory.Falconer.Fourier.ScaledInverseIntegration
import OAI.MeasureTheory.Falconer.Geometry.NormalizedSpatialFactors

namespace OAI

/-! # Exact normalized factorization of the integrated stationary inverse

The endpoint sizes are extracted before any energy estimate. All integrals
remain under the original pair laws and the exact spatial Fourier kernel.
-/

namespace Falconer
open Set MeasureTheory

theorem normalizedEndpoint_bound_restored {d : ℕ} {A : ℝ} (hA : 0 < A)
    (b : Space d → Sphere d → ℂ)
    (hb : ∀ x w, ‖normalizedEndpoint A b x w‖ ≤ 1) :
    ∀ x w, ‖b x w‖ ≤ A := by
  intro x w
  rw [← normalizedEndpoint_restore hA b x w,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hA]
  exact (mul_le_mul_of_nonneg_left (hb x w) hA.le).trans_eq (mul_one A)

theorem scaled_inverse_normalized_integration (n K : ℕ)
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) {s D : ℝ} (hs : 0 < s) (hD : 1 ≤ D)
    (μ ν : Measure (Space (n+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ L)
    (M P : ℝ) (B C : Space (n+3) → Space (n+3) → ℂ)
    (S : ℕ → SmoothSeparation (Space (n+3)) (Space (n+3)) (Space (n+3)))
    (hvalue : ∀ j ∈ Finset.range (K+1), ∀ x y (w : Sphere (n+3)),
      localInverseAmplitude n (fun v => B x v*C y v) j w = (S j).value x y w)
    (hmeas : ∀ j ∈ Finset.range (K+1), ∀ k : (S j).index,
      Measurable (Function.uncurry (fun x w => (S j).left k x w)) ∧
        Measurable (Function.uncurry (fun x w => (S j).right k x w)))
    (p q : (j : ℕ) → (S j).index → ℕ)
    (A E : (j : ℕ) → (S j).index → ℝ)
    (hA : ∀ j ∈ Finset.range (K+1), ∀ k, 0 < A j k)
    (hE : ∀ j ∈ Finset.range (K+1), ∀ k, 0 < E j k)
    (hb : ∀ j ∈ Finset.range (K+1), ∀ k x w,
      ‖normalizedEndpoint (A j k*D^(p j k)) (fun x w => (S j).left k x w) x w‖ ≤ 1)
    (hc : ∀ j ∈ Finset.range (K+1), ∀ k x w,
      ‖normalizedEndpoint (E j k*D^(q j k)) (fun x w => (S j).right k x w) x w‖ ≤ 1)
    (r : ℝ) :
    (M⁻¹*P⁻¹) • (∫ z : Space (n+3) × Space (n+3),
      scaledWeightedInverseSum n K s r (z.1-z.2) (fun v => B z.1 v*C z.2 v) ∂μ.prod ν) =
    ∑ j ∈ Finset.range (K+1), ∑ k : (S j).index,
      (((r*s)^(((n+2 : ℕ) : ℝ)/2)*((r*s)^j)⁻¹*
          (A j k*E j k*D^(p j k+q j k)) : ℝ) : ℂ)*
        spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL j)
          (spatialEndpointFamily μ M s (normalizedEndpoint (A j k*D^(p j k)) (fun x w => (S j).left k x w)))
          (spatialEndpointFamily ν P s (fun x w =>
            star (normalizedEndpoint (E j k*D^(q j k)) (fun x w => (S j).right k x w) x w))) r := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hAs (j) (hj : j ∈ Finset.range (K+1)) (k) : 0 < A j k*D^(p j k) :=
    mul_pos (hA j hj k) (pow_pos hDp _)
  have hEs (j) (hj : j ∈ Finset.range (K+1)) (k) : 0 < E j k*D^(q j k) :=
    mul_pos (hE j hj k) (pow_pos hDp _)
  rw [scaled_inverse_integration n K δ L hδ hL hs μ ν hsep M P B C S hvalue hmeas
    (fun j k => A j k*D^(p j k)) (fun j k => E j k*D^(q j k))
    (fun j hj k => (hAs j hj k).le)
    (fun j hj k => normalizedEndpoint_bound_restored (hAs j hj k) _ (hb j hj k))
    (fun j hj k => normalizedEndpoint_bound_restored (hEs j hj k) _ (hc j hj k)) r]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change _ * spatialSharedAmplitude _ (spatialEndpointFamily μ M s (fun x w => (S j).left k x w))
    (spatialEndpointFamily ν P s (fun x w => star ((S j).right k x w))) r = _
  rw [spatialSharedAmplitude_normalized _ μ ν M P s (hAs j hj k) (hEs j hj k)]
  simp only [Complex.ofReal_mul,pow_add]
  ring

end Falconer

end OAI

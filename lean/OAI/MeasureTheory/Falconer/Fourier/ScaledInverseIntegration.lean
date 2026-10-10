import OAI.MeasureTheory.Falconer.Estimates.ScaledWeightedInverse
import OAI.MeasureTheory.Falconer.Fourier.SeparatedInverseIntegration

namespace OAI

/-! # Integrating the complete cell-scaled inverse

Every term uses the original endpoint measures. The distance weight is
separated at the cell scale, and the radial coefficient is kept explicit.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def scaledInverseTerm (m j : ℕ) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+3)) : ℂ :=
  (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
    ∫ w : Sphere (m+3),
      Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
        localInverseAmplitude m (B z.1 z.2) j w ∂sphereMeasure (m+3)

theorem scaledWeightedInverseSum_eq_terms (m J : ℕ) (s r : ℝ)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+3)) :
    scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2) =
      ∑ j ∈ Finset.range (J+1),
        (((r*s)^(((m+2 : ℕ) : ℝ)/2)*((r*s)^j)⁻¹ : ℝ) : ℂ)*
          scaledInverseTerm m j s r B z := by
  unfold scaledWeightedInverseSum scaledInverseTerm
  apply Finset.sum_congr rfl
  intro j _
  simp only [dist_eq_norm,Complex.ofReal_mul,mul_assoc]

theorem scaledWeightedInverseSum_integrable (m J : ℕ) (s r δ : ℝ) (hδ : 0 < δ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s)
    (B : Space (m+3) → Space (m+3) → Space (m+3) → ℂ)
    (S : ℕ → SmoothSeparation (Space (m+3)) (Space (m+3)) (Space (m+3)))
    (hvalue : ∀ j ∈ Finset.range (J+1), ∀ x y (w : Sphere (m+3)),
      localInverseAmplitude m (B x y) j w = (S j).value x y w)
    (hmeas : ∀ j ∈ Finset.range (J+1), ∀ i : (S j).index,
      Measurable (Function.uncurry ((S j).left i)) ∧
        Measurable (Function.uncurry ((S j).right i)))
    (U V : (j : ℕ) → (S j).index → ℝ)
    (hU : ∀ j ∈ Finset.range (J+1), ∀ i, 0 ≤ U j i)
    (hbU : ∀ j ∈ Finset.range (J+1), ∀ i x (w : Sphere (m+3)), ‖(S j).left i x w‖ ≤ U j i)
    (hbV : ∀ j ∈ Finset.range (J+1), ∀ i x (w : Sphere (m+3)), ‖(S j).right i x w‖ ≤ V j i) :
    Integrable (fun z : Space (m+3) × Space (m+3) =>
      scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2)) (μ.prod ν) := by
  have ht (j : ℕ) (hj : j ∈ Finset.range (J+1)) :
      Integrable (scaledInverseTerm m j s r B) (μ.prod ν) := by
    unfold scaledInverseTerm
    simp_rw [hvalue j hj]
    exact separated_inverse_term_integrable δ hδ j s μ ν hsep
      (S j) (hmeas j hj) (U j) (V j) (hU j hj) (hbU j hj) (hbV j hj) r
  simp_rw [scaledWeightedInverseSum_eq_terms]
  exact integrable_finsetSum _ (fun j hj => (ht j hj).const_mul _)

theorem scaled_inverse_integration (m J : ℕ)
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ L)
    (M P : ℝ) (A C : Space (m+3) → Space (m+3) → ℂ)
    (S : ℕ → SmoothSeparation (Space (m+3)) (Space (m+3)) (Space (m+3)))
    (hvalue : ∀ j ∈ Finset.range (J+1), ∀ x y (w : Sphere (m+3)),
      localInverseAmplitude m (fun v => A x v*C y v) j w = (S j).value x y w)
    (hmeas : ∀ j ∈ Finset.range (J+1), ∀ i : (S j).index,
      Measurable (Function.uncurry ((S j).left i)) ∧
        Measurable (Function.uncurry ((S j).right i)))
    (U V : (j : ℕ) → (S j).index → ℝ)
    (hU : ∀ j ∈ Finset.range (J+1), ∀ i, 0 ≤ U j i)
    (hbU : ∀ j ∈ Finset.range (J+1), ∀ i x (w : Sphere (m+3)), ‖(S j).left i x w‖ ≤ U j i)
    (hbV : ∀ j ∈ Finset.range (J+1), ∀ i x (w : Sphere (m+3)), ‖(S j).right i x w‖ ≤ V j i)
    (r : ℝ) :
    (M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
      scaledWeightedInverseSum m J s r (z.1-z.2) (fun v => A z.1 v*C z.2 v) ∂μ.prod ν) =
    ∑ j ∈ Finset.range (J+1),
      (((r*s)^(((m+2 : ℕ) : ℝ)/2)*((r*s)^j)⁻¹ : ℝ) : ℂ)*
      (∑ i : (S j).index, ∫ w : Sphere (m+3), (∫ ξ : Space (m+3),
        spatialFourierCoeff (d := m+3) δ L hδ hL j ξ *
          (endpointTransform μ M (fun x w => spatialFourierPhase s ξ x*(S j).left i x w) r w *
            star (endpointTransform ν P
              (fun x w => spatialFourierPhase s ξ x*star ((S j).right i x w)) r w)))
        ∂sphereMeasure (m+3)) := by
  let B := fun x y v => A x v*C y v
  have ht (j : ℕ) (hj : j ∈ Finset.range (J+1)) :
      Integrable (scaledInverseTerm m j s r B) (μ.prod ν) := by
    unfold scaledInverseTerm
    simp_rw [show ∀ x y (w : Sphere (m+3)), localInverseAmplitude m (B x y) j w =
      (S j).value x y w from hvalue j hj]
    exact separated_inverse_term_integrable δ hδ j s μ ν (hsep.mono fun _ hz => hz.1)
      (S j) (hmeas j hj) (U j) (V j) (hU j hj) (hbU j hj) (hbV j hj) r
  change (M⁻¹*P⁻¹) • (∫ z, scaledWeightedInverseSum m J s r (z.1-z.2) (B z.1 z.2) ∂μ.prod ν) = _
  simp_rw [scaledWeightedInverseSum_eq_terms]
  rw [integral_finsetSum _ (fun j hj => (ht j hj).const_mul _),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul,← mul_smul_comm]
  congr 1
  exact separated_inverse_integration m δ L hδ hL j hs μ ν hsep M P (S j) A C
    (hvalue j hj) (hmeas j hj) (U j) (V j) (hU j hj) (hbU j hj) (hbV j hj) r

end Falconer

end OAI

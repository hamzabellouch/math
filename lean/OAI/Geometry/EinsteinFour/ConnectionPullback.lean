import OAI.Geometry.EinsteinFour.CoordinateChangeCalculus
import OAI.Geometry.EinsteinFour.CoordinateConnectionUniqueness

namespace OAI

/-! Metric compatibility under the coordinate change formula for a
connection. The matrices here are four-dimensional chart matrices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem pullback_metric_compatibility (H J K P U : Mat4)
    (h : J * K = P + U * J) :
    Kᵀ * (Jᵀ * H * J) + (Jᵀ * H * J) * K =
      Pᵀ * H * J + Jᵀ * (Uᵀ * H + H * U) * J + Jᵀ * H * P := by
  have ht : Kᵀ * Jᵀ = Pᵀ + Jᵀ * Uᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_add] using congrArg Matrix.transpose h
  calc
    _ = (Kᵀ * Jᵀ) * H * J + Jᵀ * H * (J * K) := by noncomm_ring
    _ = (Pᵀ + Jᵀ * Uᵀ) * H * J + Jᵀ * H * (P + U * J) := by rw [ht, h]
    _ = _ := by noncomm_ring

def pulledConnection (J P U : Mat4) : Mat4 := J⁻¹ * (P + U * J)

theorem pulledConnection_equation (J P U : Mat4) (hJ : IsUnit J.det) :
    J * pulledConnection J P U = P + U * J := by
  unfold pulledConnection
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv J hJ, one_mul]

theorem pulledConnection_metric_compatibility (H J P U : Mat4)
    (hJ : IsUnit J.det) :
    (pulledConnection J P U)ᵀ * (Jᵀ * H * J) +
      (Jᵀ * H * J) * pulledConnection J P U =
      Pᵀ * H * J + Jᵀ * (Uᵀ * H + H * U) * J + Jᵀ * H * P :=
  pullback_metric_compatibility H J _ P U (pulledConnection_equation J P U hJ)

def weightedConnection (J : Mat4) (C : Fin 4 → Mat4) (i : Fin 4) : Mat4 :=
  ∑ a, J a i • C a

theorem weightedConnection_torsion (J : Mat4) (C : Fin 4 → Mat4)
    (hC : ∀ a b r, C a r b = C b r a) (i j r : Fin 4) :
    (weightedConnection J C i * J) r j = (weightedConnection J C j * J) r i := by
  have he (s t : Fin 4) : (weightedConnection J C s * J) r t =
      ∑ a, ∑ b, J a s * C a r b * J b t := by
    simp only [weightedConnection, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [he, he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hC b a r]
  ring

theorem pulledConnection_torsion (J : Mat4) (P C : Fin 4 → Mat4)
    (hP : ∀ i j r, P i r j = P j r i)
    (hC : ∀ a b r, C a r b = C b r a) (i j k : Fin 4) :
    pulledConnection J (P i) (weightedConnection J C i) k j =
      pulledConnection J (P j) (weightedConnection J C j) k i := by
  change (∑ r, J⁻¹ k r * (P i r j + (weightedConnection J C i * J) r j)) =
    ∑ r, J⁻¹ k r * (P j r i + (weightedConnection J C j * J) r i)
  apply Finset.sum_congr rfl
  intro r _
  rw [hP i j r, weightedConnection_torsion J C hC i j r]

theorem matrixPartial_congruence (J A : FourSpace → Mat4) (z : FourSpace)
    (hJ : ∀ r s, DifferentiableAt ℝ (fun w => J w r s) z)
    (hA : ∀ r s, DifferentiableAt ℝ (fun w => A w r s) z) (i : Fin 4) :
    matrixPartial (fun w => (J w)ᵀ * (A w * J w)) i z =
      (matrixPartial J i z)ᵀ * A z * J z +
        (J z)ᵀ * matrixPartial A i z * J z + (J z)ᵀ * A z * matrixPartial J i z := by
  have hAJ (r s : Fin 4) :
      DifferentiableAt ℝ (fun w => (A w * J w) r s) z := by
    change DifferentiableAt ℝ (fun w => ∑ p, A w r p * J w p s) z
    exact DifferentiableAt.fun_sum (fun p _ => (hA r p).mul (hJ p s))
  rw [matrixPartial_mul (fun w => (J w)ᵀ) (fun w => A w * J w) z
      (fun r s => hJ s r) hAJ i,
    matrixPartial_transpose, matrixPartial_mul A J z hA hJ i]
  noncomm_ring

/-- The mixed Jacobian derivative cancels from the curvature transformation.
The two last premises are exactly the differentiated connection laws. -/
theorem curvature_intertwining_of_connection
    (J C₁ C₂ U₁ U₂ P₁ P₂ D₁₂ D₂₁ V₁₂ V₂₁ E : Mat4)
    (h₁ : J * C₁ = P₁ + U₁ * J) (h₂ : J * C₂ = P₂ + U₂ * J)
    (h₁₂ : P₁ * C₂ + J * D₁₂ = E + V₁₂ * J + U₂ * P₁)
    (h₂₁ : P₂ * C₁ + J * D₂₁ = E + V₂₁ * J + U₁ * P₂) :
    J * (D₁₂ - D₂₁ + C₁ * C₂ - C₂ * C₁) =
      (V₁₂ - V₂₁ + U₁ * U₂ - U₂ * U₁) * J := by
  have hd : J * D₁₂ - J * D₂₁ =
      (V₁₂ - V₂₁) * J + U₂ * P₁ - U₁ * P₂ - P₁ * C₂ + P₂ * C₁ := by
    calc
      _ = (P₁ * C₂ + J * D₁₂) - (P₂ * C₁ + J * D₂₁) -
          P₁ * C₂ + P₂ * C₁ := by noncomm_ring
      _ = _ := by rw [h₁₂, h₂₁]; noncomm_ring
  calc
    _ = (J * D₁₂ - J * D₂₁) + (J * C₁) * C₂ - (J * C₂) * C₁ := by
      noncomm_ring
    _ = ((V₁₂ - V₂₁) * J + U₂ * P₁ - U₁ * P₂ - P₁ * C₂ + P₂ * C₁) +
        (P₁ + U₁ * J) * C₂ - (P₂ + U₂ * J) * C₁ := by rw [hd, h₁, h₂]
    _ = (V₁₂ - V₂₁) * J + U₂ * P₁ - U₁ * P₂ - P₁ * C₂ + P₂ * C₁ +
        P₁ * C₂ + U₁ * (J * C₂) - P₂ * C₁ - U₂ * (J * C₁) := by noncomm_ring
    _ = _ := by rw [h₁, h₂]; noncomm_ring

end
end PositiveEinsteinFour.Geometry

end OAI

import OAI.MeasureTheory.Falconer.Estimates.DescriptorPairBudget
import OAI.MeasureTheory.Falconer.Estimates.RotatedInverseRemainder

namespace OAI

/-! # The stationary remainder for the actual masked distance Fourier transform

This is the original masked law, with its original model mass and its
cell-scale distance weight. The integrability premise is supplied by the
finite separated inverse integration theorem.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem exists_rotated_masked_fourier_inverse_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (n : ℕ) {κ Z : ℝ} (hκ : 0 < κ) :
    ∃ K : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ (T : Space (n+3) ≃ₗᵢ[ℝ] Space (n+3)), ∀ R D r δ : ℝ, 1 ≤ R → 1 ≤ D → D ≤ R^2 → 0 < δ →
      ∀ (w₀ : Sphere (n+3)) (Q : DyadicCube (n+3)) (ρ : Measure (Space (n+3)))
        [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
        (B : Finset PlanarFalconer.PolicyDescriptor)
        (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+3)))
        (X Y : DyadicCube (n+3)),
      (∀ b ∈ B, ∀ w : Sphere (n+3), ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^a) →
      (∀ᵐ z : Space (n+3) × Space (n+3) ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        ‖T (NormedSpace.normalize (z.1-z.2))-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/8) →
      (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        1 ≤ r*dist z.1 z.2 ∧ D^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      ∀ C : ℝ, 1 ≤ C →
      (∀ x y k, k ≤ 2*(K+1)+(n+2)+1 → ∀ w : Sphere (n+3),
        ‖iteratedFDeriv ℝ k (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S x y) w‖ ≤ C*D^k) →
      Integrable (fun z : Space (n+3) × Space (n+3) =>
        rotatedScaledWeightedInverseSum n K T ((2:ℝ)^a)⁻¹ r (z.1-z.2)
          (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S z.1 z.2))
        ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)) →
      ‖((profileModelMass m N a)⁻¹*(profileModelMass m N a)⁻¹) •
          (∫ z : Space (n+3) × Space (n+3),
            rotatedScaledWeightedInverseSum n K T ((2:ℝ)^a)⁻¹ r (z.1-z.2)
              (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S z.1 z.2)
            ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)) -
        charFun (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) r‖ ≤
      |(profileModelMass m N a)⁻¹*(profileModelMass m N a)⁻¹| *
        ((δ^(-(((n+2:ℕ):ℝ)/2))*A*C*R^(-Z))*
          ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)).real univ) := by
  obtain ⟨K,A,hA,hbound⟩ := exists_integrated_rotated_inverse_order hgnomonic hquadratic n (E := Z) hκ
  refine ⟨K,A,hA,?_⟩
  intro T R D r δ hR hD hDR hδ w₀ Q ρ _ m N σ J i a B S X Y hcover hsep hnear hfreq C hC hderiv hInt
  have hs : 0 < ((2:ℝ)^a)⁻¹ := by positivity
  have hsep' : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      δ ≤ dist z.1 z.2/((2:ℝ)^a)⁻¹ := by
    simpa only [div_inv_eq_mul] using hsep
  have hne : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier), z.1-z.2 ≠ 0 := by
    filter_upwards [hsep] with z hz
    have hd : 0 < dist z.1 z.2 :=
      (mul_pos_iff_of_pos_right (show 0 < (2:ℝ)^a by positivity)).mp (hδ.trans_le hz)
    exact sub_ne_zero.mpr (dist_pos.mp hd)
  rw [maskedCellDistance_fourier_scaled_kernel n w₀ Q ρ m N σ J i a B S hcover X Y hne]
  exact hbound T R D ((2:ℝ)^a)⁻¹ r δ hR hD hDR hs hδ
    (ρ.restrict X.carrier) (ρ.restrict Y.carrier) hsep' hnear hfreq
    (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B S)
    (descriptorPairAmplitude_measurable Q ρ (fun u => m (u/N)) N σ J i B S)
    (descriptorPairAmplitude_contDiff Q ρ (fun u => m (u/N)) N σ J i B S)
    C (zero_le_one.trans hC)
    (fun x y w => (descriptorPairAmplitude_norm_le Q ρ (fun u => m (u/N)) N σ J i B S x y w).trans hC)
    hderiv hInt (profileModelMass m N a) (profileModelMass m N a)

end Falconer

end OAI

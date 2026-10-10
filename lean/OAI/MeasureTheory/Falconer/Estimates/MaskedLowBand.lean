import OAI.MeasureTheory.Falconer.Estimates.MaskedNested

namespace OAI

/-! # Exact normalization of the positive low-shell reduction

There is no comparison of different model masses in this step: parent and
child retain the same start depth and the same `profileModelMass`.
-/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

 theorem masked_distance_low_band (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ)
    (σ : ℝ) (J i a v : ℕ) (hav : a ≤ v)
    (B B' : Finset PlanarFalconer.PolicyDescriptor) (hsub : B' ⊆ B)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) (X Y : DyadicCube d)
    (hsep : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      1 ≤ dist z.1 z.2*(2:ℝ)^a)
    [IsFiniteMeasure (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y)] :
    (1/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^v) ((2:ℝ)^v),
      ‖charFun (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) r‖^2 ≤
    (32*PlanarFalconer.binKernelConstant.toReal) *
      ((2:ℝ)^N)^(4*m ((a:ℝ)/N))*(2:ℝ)^(v-a) *
      ((testedCellDistance ρ ρ X Y
        (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B')).prod
        (testedCellDistance ρ ρ X Y
          (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B'))).real
            {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^v} := by
  let θ := testedCellDistance ρ ρ X Y
    (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B')
  have hdom := maskedCellDistance_le_tested w₀ Q ρ m N σ J i a B B' hsub S hcover hd X Y hsep
    (descriptorPairTests_measurable w₀ Q ρ _ N σ J (i+1) B')
  have hband := dominated_real_frequency_band
    (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) θ
    (by positivity : 0 < (2:ℝ)^v) (sq_nonneg ((profileModelMass m N a)⁻¹)) hdom
  have hm : (((profileModelMass m N a)⁻¹)^2)^2 = ((2:ℝ)^N)^(4*m ((a:ℝ)/N)) := by
    rw [← pow_mul]
    exact profileModelMass_inverse_four m N a
  rw [hm] at hband
  have hcollision : (θ.prod θ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 1/(2:ℝ)^v} ≤
      (θ.prod θ).real {z : ℝ × ℝ | |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^v} := by
    apply measureReal_mono (h₂ := measure_ne_top (θ.prod θ) _)
    intro z hz
    change |z.1-z.2| ≤ 1/(2:ℝ)^v at hz
    change |z.1-z.2| ≤ 100*((d:ℝ)+1)/(2:ℝ)^v
    apply hz.trans
    exact div_le_div_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α := ℝ) d]) (by positivity)
  have h := hband.trans (mul_le_mul_of_nonneg_left hcollision (by positivity))
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1/(2:ℝ)^a)).trans_eq
  rw [show (2:ℝ)^v = (2:ℝ)^a*(2:ℝ)^(v-a) by rw [← pow_add,Nat.add_sub_of_le hav]]
  field_simp
  rfl

end Falconer

end OAI

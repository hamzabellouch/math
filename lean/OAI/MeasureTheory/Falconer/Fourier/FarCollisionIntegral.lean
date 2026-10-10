import OAI.MeasureTheory.Falconer.Estimates.FarOriginalPartition
import OAI.MeasureTheory.Falconer.Fourier.FarTestedIntegral
import OAI.MeasureTheory.Falconer.Shells.FarPositiveSum

namespace OAI

/-! # The stationary far kernel on the original collision laws

The original four-point law is reassembled before the comparable-depth
partition. Only two free cell labels remain in the resulting collision bound.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff
open PlanarFalconer (PolicyDescriptor)

private theorem originalFourPoint_far_tested_bound {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (hQ : 0 < Q.side) (profile : ℝ → ℝ) (A : ℕ → ℝ)
    (N : ℕ) (σ : ℝ) (J i q b t : ℕ)
    (X Y : List (Fin d → Bool)) (n : ℕ)
    (U : Set ((Space d × Space d) × (Space d × Space d))) (hU : MeasurableSet U)
    (hgeo : ∀ z ∈ U,
      (256*((d:ℝ)+1)*((Q.descendant X).side/(2:ℝ)^n) < dist z.1.1 z.1.2 ∧
        dist z.1.1 z.1.2 ≤ 1024*((d:ℝ)+1)*((Q.descendant X).side/(2:ℝ)^n)) ∧
      (256*((d:ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^n) < dist z.2.1 z.2.2 ∧
        dist z.2.1 z.2.2 ≤ 1024*((d:ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^n)))
    (K : ((Space d × Space d) × (Space d × Space d)) → ℂ) (C : ℝ≥0∞)
    (hcell : ∀ u ∈ farCellPartners (Q.descendant X) ρ n,
      ∀ v ∈ farCellPartners (Q.descendant Y) ρ n,
      (∫⁻ z in U, ENNReal.ofReal ‖K z‖ ∂fourPointChildMeasure
        (Q.descendant X) (Q.descendant Y) ρ ρ u v) ≤
      C*(∫⁻ z in U,
        ENNReal.ofReal (1/(1+(2:ℝ)^t*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
        ∂(testedCellPair ρ ρ (Q.descendant (X++u.1)) (Q.descendant (X++u.2))
          (policyTestPairs w₀ Q ρ profile A N σ J i q b t)).prod
          (testedCellPair ρ ρ (Q.descendant (Y++v.1)) (Q.descendant (Y++v.2))
            (policyTestPairs w₀ Q ρ profile A N σ J i q b t)))) :
    ENNReal.ofReal ((2:ℝ)^(t-b)*((2:ℝ)^N)^(4*profile b)) *
      (∫⁻ z in U, ENNReal.ofReal ‖K z‖
        ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ) ≤
      C*(((farCellPartners (Q.descendant X) ρ n) ×ˢ
        (farCellPartners (Q.descendant Y) ρ n)).card : ℝ≥0∞)*
        PlanarFalconer.binKernelConstant *
        farCollisionMaximum w₀ Q ρ profile A N σ J i q b t X Y n := by
  rw [originalFourPointMeasure_far_partition (Q.descendant X) (Q.descendant Y)
    (Q.descendant_side_pos hQ X) (Q.descendant_side_pos hQ Y) ρ ρ n U hU hgeo,
    lintegral_finsetSum_measure, Finset.mul_sum]
  calc
    _ ≤ ∑ z ∈ farCellPartners (Q.descendant X) ρ n ×ˢ
        farCellPartners (Q.descendant Y) ρ n,
      C*(ENNReal.ofReal ((2:ℝ)^(t-b)*((2:ℝ)^N)^(4*profile b)) *
        (∫⁻ x in U,
          ENNReal.ofReal (1/(1+(2:ℝ)^t*|dist x.1.1 x.1.2-dist x.2.1 x.2.2|)^2)
          ∂(testedCellPair ρ ρ (Q.descendant (X++z.1.1)) (Q.descendant (X++z.1.2))
            (policyTestPairs w₀ Q ρ profile A N σ J i q b t)).prod
            (testedCellPair ρ ρ (Q.descendant (Y++z.2.1)) (Q.descendant (Y++z.2.2))
              (policyTestPairs w₀ Q ρ profile A N σ J i q b t)))) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hu,hv⟩ := Finset.mem_product.mp hz
      simpa only [mul_left_comm] using mul_le_mul' le_rfl (hcell z.1 hu z.2 hv)
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      simpa only [mul_assoc] using mul_le_mul' (le_refl C)
        (far_positive_kernel_sum_le w₀ Q ρ profile A N σ J i q b t X Y n (fun _ _ => U))

theorem exists_jetState_far_collision_integral (m K L M : ℕ) (hML : 2*M ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (F : Finset PolicyDescriptor) (w₀ : Sphere (m+3))
        (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) [IsFiniteMeasure ρ],
      0 < Q.side → ∀ (profile : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ)
        (J i q b t : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3))),
      PlanarFalconer.policyDescriptorList A N q b t ⊆ F →
      (∀ c ∈ F, ∀ w ∈ S c, ∀ z ∈ S c, w ≠ z → descriptorMaskRadius N σ c/2 ≤ dist w z) →
      ∀ Dq Dmask E Z : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < Z →
      1 ≤ 2*(E+Dq) → (∀ c ∈ F, (descriptorMaskRadius N σ c)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq)
        (X Y : List (Fin (m+3) → Bool)) (n : ℕ)
        (U : Set ((Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)))),
      MeasurableSet U →
      (∀ z ∈ U,
        (256*(((m+3:ℕ):ℝ)+1)*((Q.descendant X).side/(2:ℝ)^n) < dist z.1.1 z.1.2 ∧
          dist z.1.1 z.1.2 ≤ 1024*(((m+3:ℕ):ℝ)+1)*((Q.descendant X).side/(2:ℝ)^n)) ∧
        (256*(((m+3:ℕ):ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^n) < dist z.2.1 z.2.2 ∧
          dist z.2.1 z.2.2 ≤ 1024*(((m+3:ℕ):ℝ)+1)*((Q.descendant Y).side/(2:ℝ)^n))) →
      (∀ z ∈ U, (2:ℝ)^(-(b:ℝ)) ≤ dist z.1.1 z.1.2 ∧
        (2:ℝ)^(-(b:ℝ)) ≤ dist z.2.1 z.2.2 ∧
        (2*(E+Dq))^2 ≤ (2:ℝ)^t*dist z.1.1 z.1.2 ∧
        (2*(E+Dq))^2 ≤ (2:ℝ)^t*dist z.2.1 z.2.2) →
      ENNReal.ofReal ((2:ℝ)^(t-b)*((2:ℝ)^N)^(4*profile b)) *
        (∫⁻ z in U, ENNReal.ofReal ‖jetStateStationaryKernel f g w₀ Q ρ profile N σ J i S Z M
          ((2:ℝ)^t) Ψ z‖
          ∂originalFourPointMeasure (Q.descendant X) (Q.descendant Y) ρ ρ) ≤
      ENNReal.ofReal (C*(B^K*Z⁻¹)^4*(2:ℝ)^(-((m+2:ℕ):ℝ)*((t:ℝ)-b))) *
        (((farCellPartners (Q.descendant X) ρ n) ×ˢ
          (farCellPartners (Q.descendant Y) ρ n)).card : ℝ≥0∞) *
        PlanarFalconer.binKernelConstant *
        farCollisionMaximum w₀ Q ρ profile A N σ J (i+1) q b t X Y n := by
  obtain ⟨B,C,hB,hC,hbound⟩ := exists_jetState_far_tested_integral m K L M hML hΨ hs
  refine ⟨B,C,hB,hC,?_⟩
  intro F w₀ Q ρ _ hQ profile A N σ J i q b t S hHF hsep Dq Dmask E Z
    hDq hDm hZ hD hscale hE f g X Y n U hU hgeo hfreq
  apply originalFourPoint_far_tested_bound w₀ Q ρ hQ profile A N σ J (i+1) q b t
    X Y n U hU hgeo
  intro u _ v _
  simpa only [fourPointChildMeasure,Q.descendant_append,policyTestPairs,Real.rpow_natCast] using
    hbound F (PlanarFalconer.policyDescriptorList A N q b t) hHF w₀ Q ρ profile N σ J i S
      hsep Dq Dmask E Z hDq hDm hZ hD hscale hE f g t b
      ((Q.descendant X).descendant u.1) ((Q.descendant X).descendant u.2)
      ((Q.descendant Y).descendant v.1) ((Q.descendant Y).descendant v.2) U hU
      (by simpa only [Real.rpow_natCast] using hfreq)

end Falconer

end OAI

import OAI.MeasureTheory.Falconer.Shells.MaskedDistanceBounds
import OAI.MeasureTheory.Falconer.Estimates.DominatedBand

namespace OAI

/-! # Support of all old masks controls the positive low-frequency child

The old weighted law is dominated by the unweighted child restriction.
This comparison takes place before applying the scalar real-line bin bound.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem maskedCellDistance_le_tested (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B B' : Finset PlanarFalconer.PolicyDescriptor) (hsub : B' ⊆ B)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) (X Y : DyadicCube d)
    (hsep : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      1 ≤ dist z.1 z.2*(2:ℝ)^a)
    (hG : MeasurableSet (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B')) :
    maskedCellDistance w₀ Q ρ m N σ J i a B S X Y ≤
      ENNReal.ofReal ((profileModelMass m N a)⁻¹^2) •
        testedCellDistance ρ ρ X Y
          (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B') := by
  let π := (ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)
  let G := descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J (i+1) B'
  let K := ENNReal.ofReal ((profileModelMass m N a)⁻¹^2)
  have hh : π.withDensity (fun z => ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 *
      descriptorPairWeight w₀ Q ρ m N σ J i a B S z)) ≤ K • π.restrict G := by
    rw [← withDensity_const,← withDensity_indicator hG]
    apply withDensity_mono
    filter_upwards [hsep] with z hz
    by_cases hgood : z ∈ G
    · rw [indicator_of_mem hgood]
      apply ENNReal.ofReal_le_ofReal
      have hb := (descriptorPairWeight_bounds w₀ Q ρ m N σ J i a B S hcover hd
        (by norm_num : (0:ℝ) < 1) z hz).2
      simp only [Real.one_rpow] at hb
      exact mul_le_of_le_one_right (sq_nonneg _) hb
    · rw [indicator_of_notMem hgood]
      have hw : descriptorPairWeight w₀ Q ρ m N σ J i a B S z = 0 := by
        by_contra hn
        have hp : descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.1
            (normalizeToSphere w₀ (z.1-z.2)) *
            descriptorProduct Q ρ (fun u => m (u/N)) N σ J i B S z.2
            (normalizeToSphere w₀ (z.1-z.2)) ≠ 0 := by
          intro hp
          apply hn
          simp only [descriptorPairWeight,mul_assoc,hp,mul_zero]
        exact hgood (descriptorPairTests_mono w₀ Q ρ _ N σ J (i+1) hsub
          (descriptorProduct_pair_support w₀ Q ρ _ N σ J i B S hcover hp))
      simp only [hw,mul_zero,ENNReal.ofReal_zero,le_refl]
  have hm := Measure.map_mono hh
    (show Measurable (fun z : Space d × Space d => dist z.1 z.2) by fun_prop)
  rw [Measure.map_smul _ (by fun_prop)] at hm
  simpa only [maskedCellDistance,testedCellDistance,testedCellPair,K,π,G] using hm

end Falconer

end OAI

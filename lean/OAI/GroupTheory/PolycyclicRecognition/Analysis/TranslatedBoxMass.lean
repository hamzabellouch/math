import OAI.GroupTheory.PolycyclicRecognition.Geometry.CanonicalExponentialMeasure

namespace OAI

/-! # Volume ratios for translated exponential boxes -/

noncomputable section

namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

/-- Right translation preserves the measure of every set, including sets
whose measurability has not yet been established separately. -/
theorem measure_image_mul_right {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant] (S : Set G) (k : G) :
    μ ((fun x => x * k) '' S) = μ S := by
  rw [← measure_preimage_mul_right μ k ((fun x => x * k) '' S),
    Set.preimage_image_eq _ (show Function.Injective (fun x : G => x * k) from
      fun _ _ h => mul_right_cancel h)]

variable {L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

/-- Enlarging the radius of a fixed exponential box multiplies its Haar
volume by exactly the corresponding power, independently of the scale. -/
theorem exponential_box_radius_measure
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) {R : ℝ} (hR : 0 ≤ R) :
    (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (exponentialCoordinateBox (Exp ∘ e) b R) =
      ENNReal.ofReal (R ^ n) *
        (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
          (exponentialCoordinateBox (Exp ∘ e) b 1) := by
  rw [exponentialCoordinateBox_eq_cube_image (Exp ∘ e) b R hR,
    exponentialCoordinateBox_eq_cube_image (Exp ∘ e) b 1 zero_le_one]
  rw [exponential_basis_subset_measure e Exp chart hchart b₀ b,
    exponential_basis_subset_measure e Exp chart hchart b₀ b]
  rw [Real.volume_Icc_pi, Real.volume_Icc_pi]
  simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, mul_one]
  rw [ENNReal.ofReal_pow hR, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
  ring

/-- The conjugated increment lies in a small box; hence the translated
source box times that increment lies in the translated product box. -/
theorem translated_box_increment_mem {G : Type*} [Group G]
    {B R : Set G} (hprod : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ R)
    (k s : G) (hs : k * s * k⁻¹ ∈ B) {x : G}
    (hx : x ∈ (fun y => y * k) '' B) :
    x * s ∈ (fun y => y * k) '' R := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y * (k * s * k⁻¹), hprod y hy _ hs, ?_⟩
  group

end PolycyclicRecognition

end

end OAI

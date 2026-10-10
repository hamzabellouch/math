import OAI.GroupTheory.PolycyclicRecognition.Analysis.TranslatedBoxMass

namespace OAI

/-! # Positive finite mass of the unit box in an arbitrary exponential basis -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Set
open scoped Manifold ENNReal

variable {L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]

theorem exponential_box_unit_mass
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
    {n : ℕ} (b₀ b : Basis (Fin n) ℝ L) :
    let μ := Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume
    μ (exponentialCoordinateBox (Exp ∘ e) b 1) ≠ ∞ ∧
      0 < (μ (exponentialCoordinateBox (Exp ∘ e) b 1)).toReal := by
  have hd : (b₀.toMatrix b).det ≠ 0 := by
    have hh := congrArg Matrix.det (b₀.toMatrix_mul_toMatrix_flip b)
    rw [Matrix.det_mul, Matrix.det_one] at hh
    intro hz
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have he : (Measure.map ((Exp ∘ e) ∘ b₀.equivFun.symm) volume)
      (exponentialCoordinateBox (Exp ∘ e) b 1) =
      ENNReal.ofReal |(b₀.toMatrix b).det| * ENNReal.ofReal 2 ^ n := by
    rw [exponentialCoordinateBox_eq_cube_image _ _ 1 zero_le_one,
      exponential_basis_subset_measure e Exp chart hchart, Real.volume_Icc_pi]
    simp; norm_num
  dsimp only
  rw [he]
  constructor
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_pos (abs_pos.mpr hd) (pow_pos (by norm_num) _)

end PolycyclicRecognition

end

end OAI

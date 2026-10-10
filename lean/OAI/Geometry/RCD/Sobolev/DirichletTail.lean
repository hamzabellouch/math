import OAI.Geometry.RCD.Sobolev.DirichletContractions

namespace OAI

/-! # Absolute-value tails in the actual Dirichlet Sobolev space -/

open Set Filter MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Cutting off the absolute value below a nonnegative level preserves
zero boundary values and does not increase Dirichlet energy. -/
theorem exists_dirichlet_absolute_tail (Ω : Set X)
    (w : SobolevSpace.dirichlet μ hQ Ω) {t : ℝ} (ht : 0 ≤ t) :
    ∃ v : SobolevSpace.dirichlet μ hQ Ω,
      (SobolevSpace.toLp μ hQ v.val =ᵐ[μ]
        fun x => max (|SobolevSpace.toLp μ hQ w.val x|-t) 0) ∧
      energyForm μ hQ v.val v.val ≤ energyForm μ hQ w.val w.val := by
  let φ : ℝ → ℝ := fun a => max (|a|-t) 0
  have hshift : LipschitzWith 1 (fun a : ℝ => |a|-t) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, sub_sub_sub_cancel_right]
      using abs_abs_sub_abs_le a b
  have hφ : LipschitzWith 1 φ := hshift.max_const 0
  have hφ0 : φ 0 = 0 := by simp [φ, neg_nonpos.mpr ht]
  let u := SobolevSpace.compContraction μ hQ hφ hφ0 w.val
  refine ⟨⟨u, SobolevSpace.compContraction_mem_dirichlet μ hQ hφ hφ0 Ω
    w.val w.property⟩, hφ.coeFn_compLp hφ0 (SobolevSpace.toLp μ hQ w.val), ?_⟩
  rw [energyForm_self, energyForm_self]
  exact mul_le_mul_of_nonneg_left
    (SobolevSpace.energy_compContraction_le μ hQ hφ hφ0 w.val) (by norm_num)

end RegularPointCoordinates

end

end OAI

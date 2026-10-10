import OAI.Geometry.RCD.Heat.BoundedHeatSemigroup

namespace OAI

/-! # Bounded clipping approximation of square-integrable data -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

theorem clipReal_nat_tendsto (a : ℝ) :
    Tendsto (fun i : ℕ => clipReal i a) atTop (𝓝 a) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |a|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with i hi
  exact (clipReal_eq_self (i : ℝ≥0) (hN.le.trans (by exact_mod_cast hi))).symm

theorem clipReal_abs_le_self (C : ℝ≥0) (a : ℝ) : |clipReal C a| ≤ |a| := by
  simpa only [Real.dist_eq, clipReal_zero, sub_zero, NNReal.coe_one, one_mul] using
    (clipReal_lipschitz C).dist_le_mul a 0

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def boundedL2Clip (i : ℕ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (clipReal_lipschitz i).compLp (clipReal_zero i) f

theorem boundedL2Clip_coe (i : ℕ) (f : Lp ℝ 2 μ) :
    boundedL2Clip μ i f =ᵐ[μ] fun x => clipReal i (f x) :=
  (clipReal_lipschitz i).coeFn_compLp (clipReal_zero i) f

theorem boundedL2Clip_abs_le (i : ℕ) (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, |boundedL2Clip μ i f x| ≤ (i : ℝ≥0) := by
  filter_upwards [boundedL2Clip_coe μ i f] with x hx
  rw [hx]
  exact clipReal_abs_le _ _

theorem boundedL2Clip_tendsto (f : Lp ℝ 2 μ) :
    Tendsto (fun i => boundedL2Clip μ i f) atTop (𝓝 f) := by
  have hid : (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).compLp (by rfl) f = f := by
    apply Lp.ext
    exact (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).coeFn_compLp (by rfl) f
  have H := compLp_tendsto_of_pointwise μ (fun i : ℕ => clipReal_lipschitz i)
    LipschitzWith.id (fun i : ℕ => clipReal_zero i) (by rfl) clipReal_nat_tendsto f
  rwa [hid] at H

end RegularPointCoordinates

end

end OAI

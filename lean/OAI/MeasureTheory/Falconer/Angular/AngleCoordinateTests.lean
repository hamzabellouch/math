import OAI.MeasureTheory.Falconer.Angular.AngularWidths
import OAI.MeasureTheory.Falconer.Angular.AngleMaskPeriodicity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceDirection_add_pi (θ : ℝ) :
    sourceDirection (θ+Real.pi) = -sourceDirection θ := by
  simp only [sourceDirection,Real.cos_add_pi,Real.sin_add_pi]
  rw [show ((-(Real.cos θ):ℝ):ℂ)+((-(Real.sin θ):ℝ):ℂ)*Complex.I =
      -((Real.cos θ:ℂ)+(Real.sin θ:ℂ)*Complex.I) by push_cast; ring]
  exact map_neg _ _

theorem sourceDirection_dist_le (θ φ : ℝ) :
    dist (sourceDirection θ) (sourceDirection φ) ≤ 2*dist θ φ := by
  unfold sourceDirection
  rw [LinearIsometryEquiv.dist_map]
  have hc := Real.lipschitzWith_cos.dist_le_mul θ φ
  have hs := Real.lipschitzWith_sin.dist_le_mul θ φ
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hc hs
  rw [dist_eq_norm]
  have hh := Complex.norm_le_abs_re_add_abs_im
    ((Real.cos θ+Real.sin θ*Complex.I)-(Real.cos φ+Real.sin φ*Complex.I))
  simp only [Complex.sub_re,Complex.add_re,Complex.mul_I_re,Complex.ofReal_re,
    Complex.ofReal_im,neg_zero,add_zero,Complex.sub_im,Complex.add_im,
    Complex.mul_I_im,zero_add] at hh
  exact hh.trans (by rw [Real.dist_eq]; linarith)

theorem parallelAngleGood_periodic (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W T : ℝ) (θ : ℝ) :
    θ+Real.pi ∈ sourceUnitDirection ⁻¹' parallelGoodSet Q ρ g p P W T ↔
    θ ∈ sourceUnitDirection ⁻¹' parallelGoodSet Q ρ g p P W T := by
  change (parallelTestCount Q ρ g p P W (sourceDirection (θ+Real.pi)):ℝ) ≤ T ↔ _
  rw [sourceDirection_add_pi,parallelTestCount_neg]
  rfl

theorem projectionAngleGood_periodic (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W T : ℝ) (θ : ℝ) :
    θ+Real.pi ∈ sourceUnitDirection ⁻¹' projectionGoodSet Q ρ p u P W T ↔
    θ ∈ sourceUnitDirection ⁻¹' projectionGoodSet Q ρ p u P W T := by
  change (projectionTestCount Q ρ p u P W (sourceDirection (θ+Real.pi)):ℝ) ≤ T ↔ _
  rw [sourceDirection_add_pi,projectionTestCount_neg]
  rfl

end PlanarFalconer

end OAI

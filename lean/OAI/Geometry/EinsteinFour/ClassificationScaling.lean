import OAI.Geometry.EinsteinFour.Statement

namespace OAI

/-! Transport the exact metric classification across the classical
constant-rescaling identity for Riemannian distance. -/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scaledEDistance_mul (g : SmoothMetric M) (a b : ℝ) (ha : 0 ≤ a)
    (x y : M) :
    scaledEDistance g (a * b) x y =
      ENNReal.ofReal (Real.sqrt a) * scaledEDistance g b x y := by
  simp only [scaledEDistance, Real.sqrt_mul ha, ENNReal.ofReal_mul (Real.sqrt_nonneg a),
    mul_assoc]

/-- A normalization step needs only its ordinary distance-scaling law;
the final model and positive scale are then transported by this theorem. -/
theorem classified_of_constant_scaling (g h : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (hd : ∀ x y, scaledEDistance h 1 x y = scaledEDistance g c x y)
    (hh : Classified h) : Classified g := by
  obtain ⟨a, ha, hmodel⟩ := hh
  have hscale (x y : M) : scaledEDistance h a x y = scaledEDistance g (a * c) x y := by
    calc
      _ = scaledEDistance h (a * 1) x y := by rw [mul_one]
      _ = ENNReal.ofReal (Real.sqrt a) * scaledEDistance h 1 x y :=
        scaledEDistance_mul h a 1 ha.le x y
      _ = ENNReal.ofReal (Real.sqrt a) * scaledEDistance g c x y := by rw [hd]
      _ = _ := (scaledEDistance_mul g a c ha.le x y).symm
  refine ⟨a * c, mul_pos ha hc, ?_⟩
  rcases hmodel with hs | hp | hr
  · left
    obtain ⟨f, hf⟩ := hs
    exact ⟨f, fun x y => (hf x y).trans (hscale x y)⟩
  · right; left
    obtain ⟨f, hf⟩ := hp
    exact ⟨f, fun x y => (hf x y).trans (hscale x y)⟩
  · right; right
    obtain ⟨f, hf⟩ := hr
    exact ⟨f, fun x y => (hf x y).trans (hscale x y)⟩

end
end PositiveEinsteinFour

end OAI

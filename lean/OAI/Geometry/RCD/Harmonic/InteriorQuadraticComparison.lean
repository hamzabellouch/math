import OAI.Geometry.RCD.Harmonic.InteriorQuadraticDefect

namespace OAI

/-! # Stability of the interior quadratic defect under value errors -/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates

theorem abs_three_point_difference_le {θ : ℝ} (hθ0 : 0≤θ) (hθ1 : θ≤1) (a b c : ℝ) :
    |a-(1-θ)*b-θ*c|≤|a|+|b|+|c| := by
  calc
    _ ≤ |a|+|(1-θ)*b|+|θ*c| := (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = |a|+(1-θ)*|b|+θ*|c| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (show 0≤1-θ by linarith),abs_of_nonneg hθ0]
    _ ≤ _ := by nlinarith [abs_nonneg b,abs_nonneg c]

variable {X : Type*} [MetricSpace X]

theorem interiorQuadraticDefect_comparison (U V : X → ℝ) (l h t : Time)
    (hlh : (l:ℝ)<h) (ht : (t:ℝ)∈Icc (l:ℝ) h) (γ : C(Time,X)) :
    |interiorQuadraticDefect U l h t γ|≤|interiorQuadraticDefect V l h t γ|+
      |U (γ t)-V (γ t)|+|U (γ l)-V (γ l)|+|U (γ h)-V (γ h)| := by
  let θ := ((t:ℝ)-l)/((h:ℝ)-l)
  have hden : 0<(h:ℝ)-l := sub_pos.mpr hlh
  have hθ0 : 0≤θ := div_nonneg (sub_nonneg.mpr ht.1) hden.le
  have hθ1 : θ≤1 := (div_le_one hden).mpr (by linarith [ht.2])
  have he : interiorQuadraticDefect U l h t γ=interiorQuadraticDefect V l h t γ+
      ((U (γ t)-V (γ t))-(1-θ)*(U (γ l)-V (γ l))-θ*(U (γ h)-V (γ h))) := by
    dsimp only [interiorQuadraticDefect,θ]
    field_simp [hden.ne']
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by
    have hb := abs_three_point_difference_le hθ0 hθ1
      (U (γ t)-V (γ t)) (U (γ l)-V (γ l)) (U (γ h)-V (γ h))
    linarith only [hb])

end RegularPointCoordinates

end

end OAI

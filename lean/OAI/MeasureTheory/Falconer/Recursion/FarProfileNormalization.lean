import OAI.MeasureTheory.Falconer.Geometry.FarNormalization

namespace OAI

/-! # Exact conversion from positive collision to far-shell normalization -/

namespace Falconer

theorem profile_far_collision_normalization {N : ℕ} (hN : 0 < N)
    (d : ℕ) (m : ℝ → ℝ) (a b : ℕ) (v lam : ℝ) :
    ((2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass m N a)⁻¹^4*
        (2:ℝ)^(-((d:ℝ)-1)*(v-b)) /
      ((2:ℝ)^(v-b)*(profileModelMass m N b)⁻¹^4)) *
        ((2:ℝ)^N)^(2*(m ((b:ℝ)/N)-m ((a:ℝ)/N))+4*((d:ℝ)+1)*lam) =
      ((2:ℝ)^N)^(-2*((m ((b:ℝ)/N)-((d:ℝ)/2)*(b:ℝ)/N)-
        (m ((a:ℝ)/N)-((d:ℝ)/2)*(a:ℝ)/N))+4*((d:ℝ)+1)*lam) := by
  have ha : profileModelMass m N a ≠ 0 := by unfold profileModelMass; positivity
  have hb : profileModelMass m N b ≠ 0 := by unfold profileModelMass; positivity
  have hv : (2:ℝ)^(v-b) ≠ 0 := by positivity
  have hi : ((2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass m N a)⁻¹^4*
        (2:ℝ)^(-((d:ℝ)-1)*(v-b)) /
      ((2:ℝ)^(v-b)*(profileModelMass m N b)⁻¹^4)) =
      (2:ℝ)^((d:ℝ)*(v-a))*(profileModelMass m N b/profileModelMass m N a)^4*
        (2:ℝ)^(-((d:ℝ)-1)*(v-b))*(2:ℝ)^(-(v-b)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    field_simp
  rw [hi]
  exact profile_far_prefactor hN d m a b v lam

end Falconer

end OAI

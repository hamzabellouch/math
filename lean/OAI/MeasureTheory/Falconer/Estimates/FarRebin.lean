import OAI.MeasureTheory.Falconer.Geometry.FarCellGeometry
import OAI.MeasureTheory.Falconer.Recursion.DisplacementDepth

namespace OAI

/-! # A common dyadic depth for the two comparable far displacements

The scalar depth-selection argument applies to arbitrary displacements
and ambient dimensions.
-/

namespace Falconer

theorem comparable_displacement_depth_dimensional (d : ℕ)
    {d₁ d₂ : ℝ} {a h : ℕ}
    (hupper : max d₁ d₂ ≤ 2*((d:ℝ)+1)*(2:ℝ)^(-(a:ℝ)))
    (hfar : 8*((d:ℝ)+1)*(2:ℝ)^(-(h:ℝ)) < max d₁ d₂)
    (hc₁ : max d₁ d₂ ≤ 2*d₁) (hc₂ : max d₁ d₂ ≤ 2*d₂) :
    ∃ b : ℕ, a+9 ≤ b ∧ b ≤ h+6 ∧
      (256*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ)) < d₁ ∧
        d₁ ≤ 1024*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ))) ∧
      (256*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ)) < d₂ ∧
        d₂ ≤ 1024*((d:ℝ)+1)*(2:ℝ)^(-(b:ℝ))) := by
  have hd : 0 < (d:ℝ)+1 := by positivity
  have he : max (d₁/((d:ℝ)+1)) (d₂/((d:ℝ)+1)) =
      max d₁ d₂/((d:ℝ)+1) := max_div_div_right hd.le _ _
  have hu : max (d₁/((d:ℝ)+1)) (d₂/((d:ℝ)+1)) ≤ 2*(2:ℝ)^(-(a:ℝ)) := by
    rw [he]
    apply (div_le_iff₀ hd).mpr
    nlinarith [hupper]
  have hs : 16*(2:ℝ)^(-((h+1:ℕ):ℝ)) <
      max (d₁/((d:ℝ)+1)) (d₂/((d:ℝ)+1)) := by
    rw [he]
    have hp : (2:ℝ)^(-((h+1:ℕ):ℝ)) = (2:ℝ)^(-(h:ℝ))/2 := by
      rw [Nat.cast_add,Nat.cast_one,neg_add,Real.rpow_add (by norm_num)]
      norm_num [div_eq_mul_inv]
    rw [hp]
    apply (lt_div_iff₀ hd).mpr
    nlinarith [hfar]
  have hc₁' : max (d₁/((d:ℝ)+1)) (d₂/((d:ℝ)+1)) ≤ 2*(d₁/((d:ℝ)+1)) := by
    rw [he]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hc₁ hd.le
  have hc₂' : max (d₁/((d:ℝ)+1)) (d₂/((d:ℝ)+1)) ≤ 2*(d₂/((d:ℝ)+1)) := by
    rw [he]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hc₂ hd.le
  obtain ⟨b,hba,hbh,hb₁,hb₂⟩ :=
    PlanarFalconer.comparable_displacement_depth hu hs hc₁' hc₂'
  refine ⟨b,hba,by omega,?_,?_⟩
  · constructor
    · have hh := (lt_div_iff₀ hd).mp hb₁.1
      nlinarith [hh]
    · have hh := (div_le_iff₀ hd).mp hb₁.2
      nlinarith [hh]
  · constructor
    · have hh := (lt_div_iff₀ hd).mp hb₂.1
      nlinarith [hh]
    · have hh := (div_le_iff₀ hd).mp hb₂.2
      nlinarith [hh]

end Falconer

end OAI

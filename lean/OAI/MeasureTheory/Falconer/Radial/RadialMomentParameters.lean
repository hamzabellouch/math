import OAI.MeasureTheory.Falconer.Measures.StartingMeasures

namespace OAI

/-! # The fixed exponents used in Orponen's published radial moment estimate -/

namespace Falconer

theorem radial_moment_parameters {h δ : ℝ} (hh : 1 ≤ h) (hδ : 0 < δ) (hδ1 : δ < 1) :
    h < h+δ/2 ∧ h+δ/2 < h+1 ∧ 0 < h-δ/4 ∧ h-δ/4 < h ∧
    2*h-(h+δ/2) < h-δ/4 ∧ 1 < 1+δ/(8*h) ∧
    1+δ/(8*h) < 2-(h-δ/4)/h ∧
    1+δ/(8*h) < (h-δ/4)/(2*h-(h+δ/2)) := by
  have hh0 : 0 < h := by linarith only [hh]
  have hden : 0 < 2*h-(h+δ/2) := by linarith only [hh,hδ1]
  refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,?_,?_,?_⟩
  · have := div_pos hδ (mul_pos (by norm_num : (0:ℝ) < 8) hh0)
    linarith
  · have he : 2-(h-δ/4)/h = 1+δ/(4*h) := by
      field_simp
      ring
    rw [he]
    have hd := div_lt_div_of_pos_left hδ
      (by positivity : 0 < 4*h) (by linarith : 4*h < 8*h)
    linarith only [hd]
  · apply (lt_div_iff₀ hden).mpr
    have he : (1+δ/(8*h))*(2*h-(h+δ/2)) = h-3*δ/8-δ^2/(16*h) := by
      field_simp
      ring
    rw [he]
    have hn : 0 ≤ δ^2/(16*h) := by positivity
    linarith only [hδ,hn]

end Falconer

end OAI

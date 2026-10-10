import OAI.Probability.BenjaminiSchramm.PairedSprinkling

namespace OAI

noncomputable section

namespace Percolation.BenjaminiSchramm

theorem exists_sprinkling_parameter (q p : unitInterval) (hqp : q < p) (hp1 : p < 1) :
    ∃ b : unitInterval, 0 < (b : ℝ) ∧ (b : ℝ) < 1 ∧ Percolation.sprinkleParameter q b=p := by
  have hqp' : (q : ℝ) < p := hqp
  have hp1' : (p : ℝ) < 1 := hp1
  have hden : 0 < 1-(q : ℝ) := by linarith
  let b : unitInterval := ⟨((p : ℝ)-q)/(1-q),
    (div_pos (sub_pos.mpr hqp') hden).le,
    (div_le_one hden).mpr (by linarith [p.2.2])⟩
  refine ⟨b,div_pos (sub_pos.mpr hqp') hden,(div_lt_one hden).mpr (by linarith),?_⟩
  apply Subtype.ext
  change (q : ℝ)+(1-q)*(((p : ℝ)-q)/(1-q))=(p : ℝ)
  field_simp; ring

end Percolation.BenjaminiSchramm

end

end OAI

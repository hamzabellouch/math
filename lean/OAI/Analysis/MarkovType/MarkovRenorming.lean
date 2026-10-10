import OAI.Analysis.MarkovType.MarkovTransport
import OAI.Analysis.MarkovType.Renormed

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {p K : ℝ}

theorem MarkovTypeWith.of_renormed (N : EquivalentNorm X)
    (hN : MarkovTypeWith p K (Renormed N)) :
    MarkovTypeWith p ((N.upper / N.lower) * K) X := by
  apply hN.of_distortion_map (Renormed.ofOriginal N) N.lower_pos N.upper_pos
  · intro x y
    change N.lower * ‖x - y‖ ≤ N.p (x - y)
    exact N.lower_bound (x - y)
  · intro x y
    change N.p (x - y) ≤ N.upper * ‖x - y‖
    exact N.upper_bound (x - y)

theorem MarkovTypeWith.renormed (N : EquivalentNorm X)
    (hX : MarkovTypeWith p K X) :
    MarkovTypeWith p ((N.upper / N.lower) * K) (Renormed N) := by
  have h := hX.of_distortion_map (Renormed.toOriginal N)
    (inv_pos.mpr N.upper_pos) (inv_pos.mpr N.lower_pos)
  have hlo : ∀ x y : Renormed N,
      N.upper⁻¹ * ‖x - y‖ ≤
        ‖Renormed.toOriginal N x - Renormed.toOriginal N y‖ := by
    intro x y
    change N.upper⁻¹ * N.p (Renormed.toOriginal N x - Renormed.toOriginal N y) ≤
      ‖Renormed.toOriginal N x - Renormed.toOriginal N y‖
    have h := mul_le_mul_of_nonneg_left
      (N.upper_bound (Renormed.toOriginal N x - Renormed.toOriginal N y))
      (inv_pos.mpr N.upper_pos).le
    simpa only [← mul_assoc, inv_mul_cancel₀ N.upper_pos.ne', one_mul] using h
  have hhi : ∀ x y : Renormed N,
      ‖Renormed.toOriginal N x - Renormed.toOriginal N y‖ ≤ N.lower⁻¹ * ‖x - y‖ := by
    intro x y
    change ‖Renormed.toOriginal N x - Renormed.toOriginal N y‖ ≤
      N.lower⁻¹ * N.p (Renormed.toOriginal N x - Renormed.toOriginal N y)
    have h := mul_le_mul_of_nonneg_left
      (N.lower_bound (Renormed.toOriginal N x - Renormed.toOriginal N y))
      (inv_pos.mpr N.lower_pos).le
    simpa only [← mul_assoc, inv_mul_cancel₀ N.lower_pos.ne', one_mul] using h
  simpa only [inv_div_inv] using h hlo hhi

theorem hasMarkovType_renormed_iff (N : EquivalentNorm X) :
    HasMarkovType p (Renormed N) ↔ HasMarkovType p X := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨(N.upper / N.lower) * K, hK.of_renormed N⟩
  · rintro ⟨K, hK⟩
    exact ⟨(N.upper / N.lower) * K, hK.renormed N⟩

theorem hasNontrivialMarkovType_renormed_iff (N : EquivalentNorm X) :
    HasNontrivialMarkovType (Renormed N) ↔ HasNontrivialMarkovType X := by
  simp only [HasNontrivialMarkovType, hasMarkovType_renormed_iff N]

end MarkovSuperreflexivity

end

end OAI

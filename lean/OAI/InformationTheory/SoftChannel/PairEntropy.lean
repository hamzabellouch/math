import OAI.InformationTheory.BooleanNoise.PairEntropy
import OAI.InformationTheory.SoftChannel.CurvatureBounds

namespace OAI

section

noncomputable section

namespace LeanBlast.CourtadeKumar

theorem PairEntropy_div_mem_Ioo (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    b / s ∈ Set.Ioo (-1) 1 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  constructor
  · apply (lt_div_iff₀ hs).2
    linarith
  · apply (div_lt_iff₀ hs).2
    linarith

theorem PairEntropy_weighted_psi_div (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    s / 2 * psi (b / s) =
      (s + b) / 4 * Real.log (s + b) + (s - b) / 4 * Real.log (s - b) -
        s / 2 * Real.log s := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hp : s + b ≠ 0 := ne_of_gt (by linarith)
  have hm : s - b ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 + b / s = (s + b) / s := by field_simp
  have hminus : 1 - b / s = (s - b) / s := by field_simp
  rw [psi, hplus, hminus, Real.log_div hp hs0, Real.log_div hm hs0]
  field_simp
  ring

theorem PairEntropy_pair_artanh_eq_log_sub (x : ℝ) (hx : x ∈ Set.Ioo (-1) 1) :
    Real.artanh x = (Real.log (1 + x) - Real.log (1 - x)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨le_of_lt hx.1, le_of_lt hx.2⟩,
    Real.log_div (ne_of_gt (by linarith [hx.1])) (ne_of_gt (by linarith [hx.2]))]
  ring

theorem PairEntropy_artanh_div (s b : ℝ) (hs : 0 < s) (hb : |b| < s) :
    Real.artanh (b / s) = (Real.log (s + b) - Real.log (s - b)) / 2 := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hb
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hp : s + b ≠ 0 := ne_of_gt (by linarith)
  have hm : s - b ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 + b / s = (s + b) / s := by field_simp
  have hminus : 1 - b / s = (s - b) / s := by field_simp
  rw [PairEntropy_pair_artanh_eq_log_sub _ (PairEntropy_div_mem_Ioo s b hs hb), hplus, hminus,
    Real.log_div hp hs0, Real.log_div hm hs0]
  ring

end LeanBlast.CourtadeKumar
end
end

end OAI

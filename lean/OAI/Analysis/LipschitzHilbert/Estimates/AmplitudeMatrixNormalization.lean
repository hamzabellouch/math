import OAI.Analysis.LipschitzHilbert.Estimates.FiniteMatrixDiscard

namespace OAI

noncomputable section
namespace LipschitzHilbert

theorem weighted_pair_bound_normalized (z : ℂ) (a b K m n F E : ℝ)
    (ha : 0≤a) (hb : 0≤b) (hm : 0≤m) (hn : 0≤n) (hF : 0<F) (hE : 0<E)
    (hz : ‖z‖≤K*Real.sqrt m*Real.sqrt n) :
    ‖(a*b) • z‖≤(K*Real.sqrt F*Real.sqrt E)*
      (a*Real.sqrt (m/F))*(b*Real.sqrt (n/E)) := by
  rw [norm_smul,Real.norm_of_nonneg (mul_nonneg ha hb)]
  apply (mul_le_mul_of_nonneg_left hz (mul_nonneg ha hb)).trans_eq
  rw [Real.sqrt_div hm,Real.sqrt_div hn]
  field_simp [(Real.sqrt_pos.2 hF).ne',(Real.sqrt_pos.2 hE).ne']

end LipschitzHilbert

end

end OAI

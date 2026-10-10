import OAI.Probability.InvariantIsing.Spectral.SpectralExcess

namespace OAI

/-! Multiplication by a real coupling transports the spectral interval and its error. -/
noncomputable section
namespace InvariantIsing

lemma spectralExcess_scale_le {N : ℕ} (eig : Fin N → ℝ) (a b c : ℝ) :
    spectralExcess (fun i => c*eig i) (min (c*a) (c*b)) (max (c*a) (c*b)) ≤
      |c| * spectralExcess eig a b := by
  have he := spectralExcess_nonneg eig a b
  apply spectralExcess_le _ _ _ _ (mul_nonneg (abs_nonneg c) he)
  intro i
  have h := spectralExcess_bounds eig a b i
  by_cases hc : 0 ≤ c
  · rw [abs_of_nonneg hc]
    have hl := mul_le_mul_of_nonneg_left h.1 hc
    have hu := mul_le_mul_of_nonneg_left h.2 hc
    constructor
    · nlinarith [min_le_left (c*a) (c*b)]
    · nlinarith [le_max_right (c*a) (c*b)]
  · have hc' : c ≤ 0 := le_of_not_ge hc
    rw [abs_of_nonpos hc']
    have hl := mul_le_mul_of_nonpos_left h.1 hc'
    have hu := mul_le_mul_of_nonpos_left h.2 hc'
    constructor
    · nlinarith [min_le_right (c*a) (c*b)]
    · nlinarith [le_max_left (c*a) (c*b)]

end InvariantIsing

end

end OAI

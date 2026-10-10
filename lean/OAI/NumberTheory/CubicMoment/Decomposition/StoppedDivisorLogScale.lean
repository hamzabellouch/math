import OAI.NumberTheory.CubicMoment.Decomposition.StoppedCoreScale

namespace OAI

/-! Logarithmic choices for the two nonempty-divisor error terms. -/
noncomputable section
namespace CubicFirstMoment

lemma rough_cutoff_log_saving {L R : ℝ} (hL : 0 < L) (v k : ℕ)
    (hR : 2*L^(2*(v+k)) ≤ R) :
    L^v*(R/2)^(-(1/2:ℝ)) ≤ 1/L^k := by
  have hlower : L^(2*(v+k)) ≤ R/2 := by linarith
  have hp := Real.rpow_le_rpow_of_nonpos (pow_pos hL _) hlower
    (show -(1/2:ℝ) ≤ 0 by norm_num)
  apply (mul_le_mul_of_nonneg_left hp (pow_nonneg hL.le _)).trans_eq
  rw [←Real.rpow_natCast L (2*(v+k)),←Real.rpow_mul hL.le]
  have he : ((2*(v+k):ℕ):ℝ)*(-(1/2:ℝ)) = -((v+k:ℕ):ℝ) := by
    push_cast
    ring
  rw [he,Real.rpow_neg hL.le,Real.rpow_natCast,pow_add]
  field_simp

lemma stopped_hybrid_weighted_scale {b L I C H C₁ C₂ C₃ : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hC : 0 ≤ C) (k : ℕ)
    (hI : 0 ≤ I) (hcount : I ≤ C*L^2)
    (hpower : b^(-(1/20000:ℝ))*L^(k+2) ≤ H)
    (hC₁ : C₁ ≤ C₃) (hC₂ : C₂ ≤ C₃) (hC₃ : 0 ≤ C₃) :
    I*(b^2*((L^(4*(k+2)))/5832)^(-(1/4:ℝ))*C₁+
      b^(2-1/20000:ℝ)*C₂) ≤
    C₃*C*((5832:ℝ)^(1/4:ℝ)+H)*b^2/L^k := by
  have hp := stopped_large_core_scale hb hL hC k hcount hpower
  have he : b^(1-1/20000:ℝ)*b = b^(2-1/20000:ℝ) := by
    nth_rw 2 [←Real.rpow_one b]
    rw [←Real.rpow_add hb]
    congr 1
    ring
  calc
    _ ≤ I*(b^2*((L^(4*(k+2)))/5832)^(-(1/4:ℝ))*C₃+
        b^(2-1/20000:ℝ)*C₃) := by gcongr
    _ = C₃*(I*(b*((L^(4*(k+2)))/5832)^(-(1/4:ℝ))+
        b^(1-1/20000:ℝ))*b) := by rw [←he]; ring
    _ ≤ C₃*(C*((5832:ℝ)^(1/4:ℝ)+H)*b^2/L^k) :=
      mul_le_mul_of_nonneg_left hp hC₃
    _ = _ := by ring

end CubicFirstMoment

end

end OAI

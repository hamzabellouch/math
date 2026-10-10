import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryScalarBounds

namespace OAI

/-! # Logarithmic bin-count factors against the prime threshold -/
namespace JointDickman

lemma auxiliary_threshold_log_weight {k L c u v : ℝ}
    (hk0 : 0 ≤ k) (hk : k ≤ L*u) (hc : 0 < c) (hu : 1 ≤ u)
    (hv : 1 ≤ v) (hcv : c*u ≤ v) :
    k^2*((v^10)⁻¹)^2*u ≤ L^2/c^4/u := by
  have hu0 : 0 < u := by linarith
  have hcu : 0 < c*u := mul_pos hc hu0
  have ht := (auxiliary_threshold_bounds hv).2.trans
    (one_div_le_one_div_of_le (pow_pos hcu 4)
      (pow_le_pow_left₀ hcu.le hcv 4))
  calc
    _ ≤ (L*u)^2*(1/(c*u)^4)*u := by gcongr
    _ = _ := by field_simp

lemma auxiliary_cofactor_log_weight {k L c u v : ℝ}
    (hk0 : 0 ≤ k) (hk : k ≤ L*u) (hc : 0 < c) (hu : 1 ≤ u)
    (hcv : c*u ≤ v) : k^2/v^2 ≤ L^2/c^2 := by
  have hu0 : 0 < u := by linarith
  have hcu : 0 < c*u := mul_pos hc hu0
  calc
    _ ≤ (L*u)^2/(c*u)^2 := by gcongr
    _ = _ := by field_simp

lemma auxiliary_cross_log_weight {k L u v H : ℝ}
    (hk0 : 0 ≤ k) (hk : k ≤ L*u) (hu : 1 ≤ u) (hv : 1 ≤ v) (hH : 0 ≤ H) :
    k^2*((v^10)⁻¹)^2*(H*u^2+1) ≤ L^2*(H+1)*u^4 := by
  have hhu : H*u^2+1 ≤ (H+1)*u^2 := by nlinarith
  calc
    _ ≤ (L*u)^2*1*((H+1)*u^2) := by
      gcongr
      exact (auxiliary_threshold_bounds hv).1
    _ = _ := by ring

end JointDickman

end OAI

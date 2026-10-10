import OAI.NumberTheory.JointDickman.Amplification.AuxiliaryLogWeights

namespace OAI

/-! # A uniform scalar envelope for every auxiliary bin -/
namespace JointDickman

theorem auxiliary_cost_bound {N : ℕ} {T a b C H L c β k : ℝ}
    (hN : 0 < (N:ℝ)) (hlog : 1 ≤ Real.log (N:ℝ))
    (hT : 0 ≤ T) (hTN : T ≤ N) (ha : 0 ≤ a) (haβ : a ≤ (N:ℝ)^β)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hc : 0 < c)
    (hv : 1 ≤ Real.log a) (hcv : c*Real.log (N:ℝ) ≤ Real.log a)
    (hk0 : 0 ≤ k) (hk : k ≤ L*Real.log (N:ℝ)) :
    k^2*auxiliarySampleCost C H N N T a b ≤
      48000*(8*L^2/c^4/Real.log (N:ℝ)+
        2*L^2*(H+1)*(Real.log (N:ℝ))^4*(N:ℝ)^(β-1/12))+
      L^2*b^2*C/c^2 := by
  let u := Real.log (N:ℝ)
  let v := Real.log a
  let τ := ((v^10)⁻¹)^2
  have hu : 1 ≤ u := hlog
  have ht0 : 0 ≤ τ := by dsimp [τ]; positivity
  have hfreq := auxiliary_frequency_log hlog hN hT hTN
  have hfirst : k^2*τ*(2*(1+Real.log (2*T+1))) ≤ 8*L^2/c^4/u := by
    calc
      _ ≤ k^2*τ*(8*u) := mul_le_mul_of_nonneg_left hfreq (by positivity)
      _ = 8*(k^2*τ*u) := by ring
      _ ≤ 8*(L^2/c^4/u) := mul_le_mul_of_nonneg_left
        (auxiliary_threshold_log_weight hk0 hk hc hu hv hcv) (by norm_num)
      _ = _ := by ring
  have hscale : (N:ℝ)^(5/12:ℝ)*Real.sqrt (2*T)*a/N ≤ 2*(N:ℝ)^(β-1/12) := by
    apply le_trans _ (auxiliary_exceptional_power hN ha haβ)
    gcongr
  have hsecond : k^2*τ*((H*u^2+1)*(N:ℝ)^(5/12:ℝ)*Real.sqrt (2*T)*a/N) ≤
      2*L^2*(H+1)*u^4*(N:ℝ)^(β-1/12) := by
    calc
      _ = (k^2*τ*(H*u^2+1))*((N:ℝ)^(5/12:ℝ)*Real.sqrt (2*T)*a/N) := by ring
      _ ≤ (L^2*(H+1)*u^4)*(2*(N:ℝ)^(β-1/12)) := by
        apply mul_le_mul (auxiliary_cross_log_weight hk0 hk hu hv hH) hscale
        · positivity
        · positivity
      _ = _ := by ring
  have hthird : k^2*(b^2*(C/v^2)) ≤ L^2*b^2*C/c^2 := by
    calc
      _ = b^2*C*(k^2/v^2) := by ring
      _ ≤ b^2*C*(L^2/c^2) := mul_le_mul_of_nonneg_left
        (auxiliary_cofactor_log_weight hk0 hk hc hu hcv) (by positivity)
      _ = _ := by ring
  calc
    _ = 48000*(k^2*τ*(2*(1+Real.log (2*T+1)))+
      k^2*τ*((H*u^2+1)*(N:ℝ)^(5/12:ℝ)*Real.sqrt (2*T)*a/N))+
      k^2*(b^2*(C/v^2)) := by dsimp [auxiliarySampleCost,u,v,τ]; ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
      (by norm_num)) hthird

end JointDickman

end OAI

import OAI.Analysis.LipschitzHilbert.Estimates.TopLogAbsorption

namespace OAI

/-! The squared logarithmic loss in moving endpoint weights is absorbed
by four inverse powers of the original positive top weight. -/

noncomputable section
namespace LipschitzHilbert

theorem top_inverse_log_squared_absorption {h S C Q a : ℝ}
    (hh : 0 < h) (hhS : h ≤ S) (hC : 1 ≤ C) (hhC : h ≤ C)
    (hQ : 0 ≤ Q) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    h^(-a)*(1+Q*Real.log (S/h))^2 ≤
      C^4*(1+Q*(Real.log (max 1 S)+1))^2*h^(-(4:ℝ)) := by
  have hS : 0 < S := hh.trans_le hhS
  have hlog : 0 ≤ Real.log (S/h) := Real.log_nonneg ((one_le_div hh).mpr hhS)
  have hlogS : 0 ≤ Real.log (max 1 S) := Real.log_nonneg (le_max_left _ _)
  have hlinear : h*(1+Q*Real.log (S/h)) ≤
      C*(1+Q*(Real.log (max 1 S)+1)) := by
    have hb := top_log_absorption (q := 2) (d := 1) hh hS hC hhC hQ
      (by norm_num) (by norm_num)
    apply (mul_le_mul_iff_left₀ hh).mp
    convert hb using 1 <;> simp
    ring
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ h*(1+Q*Real.log (S/h))) hlinear 2
  have hp : h^(2-a) ≤ C^2 := by
    apply (Real.rpow_le_rpow hh.le hhC (by linarith : 0 ≤ 2-a)).trans
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hC
    norm_num
    linarith
  have heq : h^(4-a) = h^(2-a)*h^2 := by
    rw [← Real.rpow_natCast h 2, ← Real.rpow_add hh]
    congr 1
    norm_num
    ring
  have hmain : h^(4-a)*(1+Q*Real.log (S/h))^2 ≤
      C^4*(1+Q*(Real.log (max 1 S)+1))^2 := by
    calc
      _ = h^(2-a)*(h*(1+Q*Real.log (S/h)))^2 := by rw [heq]; ring
      _ ≤ C^2*(C*(1+Q*(Real.log (max 1 S)+1)))^2 :=
        mul_le_mul hp hsq (sq_nonneg _) (sq_nonneg C)
      _ = _ := by ring
  have hsplit : h^(-a) = h^(-(4:ℝ))*h^(4-a) := by
    rw [← Real.rpow_add hh]
    congr 1
    ring
  calc
    _ = h^(-(4:ℝ))*(h^(4-a)*(1+Q*Real.log (S/h))^2) := by rw [hsplit]; ring
    _ ≤ h^(-(4:ℝ))*(C^4*(1+Q*(Real.log (max 1 S)+1))^2) :=
      mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hh.le _)
    _ = _ := by ring

/-- The precise polynomial produced by moving endpoint variation has the
four-inverse-power envelope used in the amplitude-motion argument. -/
theorem moving_weight_budget_absorption {A h S C Q a δ ε V : ℝ}
    (hh : 0 < h) (hhS : h ≤ S) (hC : 1 ≤ C) (hhC : h ≤ C)
    (hQ : 0 ≤ Q) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hV : 0 ≤ V) (hVQ : V ≤ Q*Real.log (S/h))
    (hA : A ≤ (Real.exp (a*δ)*h^(-a))*((a*δ+ε*V)+ε*V+(a*δ+ε*V)*V)) :
    A ≤ Real.exp (a*δ)*(δ+ε)*C^4*(1+Q*(Real.log (max 1 S)+1))^2*h^(-(4:ℝ)) := by
  have hpoly : (a*δ+ε*V)+ε*V+(a*δ+ε*V)*V ≤ (δ+ε)*(1+V)^2 := by
    have haδ := mul_le_mul_of_nonneg_right ha1 hδ
    have hlinear := mul_le_mul_of_nonneg_right haδ (by positivity : 0 ≤ 1+V)
    have hquad : ε*V*(2+V) ≤ ε*(1+V)^2 := by nlinarith
    have hδquad : δ*(1+V) ≤ δ*(1+V)^2 := by
      have hx : 1+V ≤ (1+V)^2 := by nlinarith
      exact mul_le_mul_of_nonneg_left hx hδ
    nlinarith
  have hsquare : (1+V)^2 ≤ (1+Q*Real.log (S/h))^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have htop := top_inverse_log_squared_absorption hh hhS hC hhC hQ ha0 ha1
  calc
    A ≤ (Real.exp (a*δ)*h^(-a))*((a*δ+ε*V)+ε*V+(a*δ+ε*V)*V) := hA
    _ ≤ (Real.exp (a*δ)*h^(-a))*((δ+ε)*(1+V)^2) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = (Real.exp (a*δ)*(δ+ε))*(h^(-a)*(1+V)^2) := by ring
    _ ≤ (Real.exp (a*δ)*(δ+ε))*(h^(-a)*(1+Q*Real.log (S/h))^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsquare
        (Real.rpow_nonneg hh.le _)) (by positivity)
    _ ≤ (Real.exp (a*δ)*(δ+ε))*(C^4*(1+Q*(Real.log (max 1 S)+1))^2*h^(-(4:ℝ))) :=
      mul_le_mul_of_nonneg_left htop (by positivity)
    _ = _ := by ring

end LipschitzHilbert

end

end OAI

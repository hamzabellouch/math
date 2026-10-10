import OAI.Analysis.LpDimension.RampSum

namespace OAI

noncomputable section
open MeasureTheory Filter ProbabilityTheory Set Finset Matrix
open scoped BigOperators Topology Matrix ENNReal NNReal RealInnerProductSpace
universe u

namespace SubpolynomialLp

lemma global_cutoff_tail (p C J : ℝ) (hC : 0 < C) (hJ : 0 < J)
    (n : ℕ) (hn : 2 ≤ n) :
    let H := 4*Real.log (n:ℝ)
    let T := 2*J*(p*Real.log J+H+Real.log (C+1))
    C*J^p*Real.exp (-T/(2*J))*(n:ℝ)^2 ≤ 1 := by
  dsimp only
  let H := 4*Real.log (n:ℝ)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_natCast_nonneg n
  have hnum : (n:ℝ)^2 ≤ Real.exp H := by
    calc
      _ = Real.exp (2*Real.log (n:ℝ)) := by
        simpa only [Nat.cast_ofNat, Real.exp_log hn0] using (Real.exp_nat_mul (Real.log (n:ℝ)) 2).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [H]; linarith)
  have he : J^p*Real.exp (-(2*J*(p*Real.log J+H+Real.log (C+1)))/(2*J)) = Real.exp (-H)/(C+1) := by
    rw [neg_div,mul_div_cancel_left₀ _ (show 2*J ≠ 0 by positivity),Real.rpow_def_of_pos hJ,← Real.exp_add]
    rw [show Real.log J*p+ -(p*Real.log J+H+Real.log (C+1)) = -H-Real.log (C+1) by ring,
      Real.exp_sub,Real.exp_log (by positivity : 0 < C+1)]
  have hE : Real.exp (-H)*(n:ℝ)^2 ≤ 1 := by
    calc
      _ ≤ Real.exp (-H)*Real.exp H := mul_le_mul_of_nonneg_left hnum (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  have hfrac : 0 ≤ C/(C+1) := by positivity
  have hfrac1 : C/(C+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  calc
    _ = C*(J^p*Real.exp (-(2*J*(p*Real.log J+H+Real.log (C+1)))/(2*J)))*(n:ℝ)^2 := by ring
    _ = (C/(C+1))*(Real.exp (-H)*(n:ℝ)^2) := by rw [he]; ring
    _ ≤ C/(C+1) := by nlinarith
    _ ≤ 1 := hfrac1

lemma ramp_cutoff_envelope (p C U L r : ℝ) (hp : 0 < p) (hC : 0 < C)
    (hU : 0 < U) (hL : 1 ≤ L) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ H : ℝ, 1 ≤ H →
      let m := ⌈L*(H^r+1)⌉₊+1
      let J := (U+1)*H*2^(2*(2*m))
      let T := 2*J*(p*Real.log J+H+Real.log (C+1))
      1 ≤ J ∧ 0 ≤ T ∧ T ≤ H^2*Real.exp (A*(H^r+1)) := by
  let B := 4*Real.log 2*(L+2)
  have hB : 0 < B := by dsimp [B]; positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  let B₂ := p*(U+2+2*B)+C+2
  have hB₂ : 0 < B₂ := by dsimp [B₂]; positivity
  let M := 2*(U+1)*B₂
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨B+M+1,by positivity,fun H hH => ?_⟩
  dsimp only
  let m := ⌈L*(H^r+1)⌉₊+1
  let J := (U+1)*H*2^(2*(2*m))
  let T := 2*J*(p*Real.log J+H+Real.log (C+1))
  have hH0 : 0 < H := by linarith
  have hHr : 1 ≤ H^r := Real.one_le_rpow hH hr0.le
  have hHrH : H^r ≤ H := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hH hr1.le
  have hm : (m:ℝ) ≤ (L+2)*(H^r+1) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ L*(H^r+1) by positivity)
    dsimp [m]
    push_cast
    nlinarith
  have hpow1 : (1:ℝ) ≤ 2^(2*(2*m)) := one_le_pow₀ (by norm_num)
  have hJ1 : 1 ≤ J := by
    have hHpow : H ≤ H*2^(2*(2*m)) := le_mul_of_one_le_right hH0.le hpow1
    dsimp [J]
    nlinarith [mul_nonneg hU.le (show 0 ≤ H*2^(2*(2*m)) by positivity)]
  have hJ : 0 < J := by linarith
  have hpow : (2:ℝ)^(2*(2*m)) ≤ Real.exp (B*(H^r+1)) := by
    calc
      _ = Real.exp ((2*(2*m):ℕ)*Real.log 2) := by rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ) < 2)]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4*Real.log 2 by positivity [Real.log_pos (by norm_num : (1:ℝ) < 2)])
        dsimp [B]
        push_cast
        nlinarith
  have hJbound : J ≤ (U+1)*H*Real.exp (B*(H^r+1)) := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hlogJ : Real.log J ≤ (U+2+2*B)*H := by
    have hh := Real.log_le_log hJ hJbound
    rw [Real.log_mul (by positivity : (U+1)*H ≠ 0) (Real.exp_ne_zero _),Real.log_exp,
      Real.log_mul (by positivity : U+1 ≠ 0) hH0.ne'] at hh
    have hu := Real.log_le_sub_one_of_pos (show 0 < U+1 by positivity)
    have hhlog := Real.log_le_sub_one_of_pos hH0
    have hr := mul_le_mul_of_nonneg_left hHrH hB.le
    have hb := mul_le_mul_of_nonneg_left hH hB.le
    have huH := mul_le_mul_of_nonneg_left hH (show 0 ≤ U+1 by positivity)
    nlinarith
  have hinside : p*Real.log J+H+Real.log (C+1) ≤ B₂*H := by
    have hpJ := mul_le_mul_of_nonneg_left hlogJ hp.le
    have hc := Real.log_le_sub_one_of_pos (show 0 < C+1 by positivity)
    have hcH := mul_le_mul_of_nonneg_left hH (show 0 ≤ C+1 by positivity)
    dsimp [B₂]
    nlinarith
  have hT0 : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg (by positivity) (by positivity [Real.log_nonneg hJ1,Real.log_nonneg (show 1 ≤ C+1 by linarith)])
  refine ⟨hJ1,hT0,?_⟩
  have hTbound : T ≤ M*H^2*Real.exp (B*(H^r+1)) := by
    calc
      _ ≤ (2*J)*(B₂*H) := mul_le_mul_of_nonneg_left hinside (by positivity)
      _ ≤ (2*((U+1)*H*Real.exp (B*(H^r+1))))*(B₂*H) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJbound (by norm_num)) (by positivity)
      _ = _ := by dsimp [M]; ring
  have hfactor : M*Real.exp (B*(H^r+1)) ≤ Real.exp ((B+M+1)*(H^r+1)) := by
    calc
      _ ≤ Real.exp M*Real.exp (B*(H^r+1)) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp M]) (Real.exp_pos _).le
      _ = Real.exp (M+B*(H^r+1)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  exact hTbound.trans (by nlinarith [mul_le_mul_of_nonneg_left hfactor (sq_nonneg H)])

end SubpolynomialLp

end

end OAI

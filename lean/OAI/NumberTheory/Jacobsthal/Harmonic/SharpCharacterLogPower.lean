import OAI.NumberTheory.Jacobsthal.Estimates.RecoveryScale

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology

theorem sharp_character_log_power (A M : ℝ) (hA : 0 < A) (hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q), chi ≠ 1 → (q:ℝ) ≤ (Real.log X)^A →
      ‖sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X‖ ≤
        K*X/(Real.log X)^M := by
  let k : ℝ := M+1
  have hk : 0 < k := by dsimp only [k]; linarith
  obtain ⟨C,hC,hRiesz⟩ := riesz_character_log_power A (2*k) hA (by positivity)
  obtain ⟨X0,hX0⟩ := eventually_atTop.1 hRiesz
  refine ⟨5*C+4,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop X0,eventually_log_rpow_le_self k] with X hthreshold hscale
  intro q _ chi hchi hq
  obtain ⟨hX3,hpowX⟩ := hscale
  let L : ℝ := Real.log X
  let delta : ℝ := L^(-k)
  let Y : ℝ := (1+delta)*X
  let f : ℕ → ℂ := fun n => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)
  obtain ⟨hd,hd1,hdX,hXY,hY2,hlogs,hlogY⟩ := recovery_scale_bounds k hk hX3 hpowX
  have hXp : 0 < X := by linarith
  have hL1 : 1 ≤ L := ((Real.lt_log_iff_exp_lt hXp).mpr (Real.exp_one_lt_three.trans_le hX3)).le
  have hLp : 0 < L := by linarith
  have hYp : 0 < Y := hXp.trans_le hXY
  have hlogYp : 0 < Real.log Y := hLp.trans_le hlogs
  have hqY : (q:ℝ) ≤ (Real.log Y)^A :=
    hq.trans (Real.rpow_le_rpow hLp.le hlogs hA.le)
  have hx := hX0 X hthreshold q chi hchi hq
  have hy := hX0 Y (hthreshold.trans hXY) q chi hchi hqY
  change ‖rieszSum f X‖ ≤ C*X/L^(2*k) at hx
  have hden : 0 < L^(2*k) := Real.rpow_pos_of_pos hLp _
  have hdenY : L^(2*k) ≤ (Real.log Y)^(2*k) := Real.rpow_le_rpow hLp.le hlogs (by positivity)
  have hy' : ‖rieszSum f Y‖ ≤ 2*C*X/L^(2*k) := by
    calc
      _ ≤ C*Y/(Real.log Y)^(2*k) := hy
      _ ≤ C*Y/L^(2*k) := div_le_div_of_nonneg_left (by positivity) hden hdenY
      _ ≤ C*(2*X)/L^(2*k) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hY2 hC.le) hden.le
      _ = _ := by ring
  have hnum : (1+delta)*‖rieszSum f Y‖+‖rieszSum f X‖ ≤ 5*C*X/L^(2*k) := by
    have h1 := mul_le_mul_of_nonneg_left hy' (show 0 ≤ 1+delta by linarith)
    have h2 := mul_le_mul_of_nonneg_right (show 1+delta ≤ 2 by linarith) (show 0 ≤ 2*C*X/L^(2*k) by positivity)
    apply (add_le_add (h1.trans h2) hx).trans_eq
    ring
  have hproduct : delta*L^(2*k) = L^k := recovery_power_product hLp k
  have hterm : ((1+delta)*‖rieszSum f Y‖+‖rieszSum f X‖)/delta ≤ 5*C*X/L^M := by
    calc
      _ ≤ (5*C*X/L^(2*k))/delta := div_le_div_of_nonneg_right hnum hd.le
      _ = 5*C*X/L^k := by rw [div_div,mul_comm (L^(2*k)) delta,hproduct]
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hLp M)
        (Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp only [k]; linarith))
  have hdeltaL : delta*L = L^(-M) := recovery_power_times_log hLp M
  have htail : (delta*X+1)*Real.log Y ≤ 4*X/L^M := by
    calc
      _ ≤ (2*delta*X)*(2*L) := mul_le_mul (by nlinarith only [hdX]) hlogY hlogYp.le (by positivity)
      _ = 4*X*(delta*L) := by ring
      _ = 4*X*L^(-M) := by rw [hdeltaL]
      _ = _ := by rw [Real.rpow_neg hLp.le,div_eq_mul_inv]
  have hcoeff : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ Real.log (n:ℝ) := fun n _ => character_vonMangoldt_norm_le chi n
  have hsharp := sharpSum_norm_le_riesz f hcoeff (show 1 ≤ X by linarith) hd
  change ‖sharpSum f X‖ ≤ (5*C+4)*X/L^M
  apply (hsharp.trans (add_le_add hterm htail)).trans_eq
  ring

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI

import OAI.NumberTheory.TwoPoint.Fourier.ModFivePrincipalPsi

namespace OAI

/-! The principal twisted Mangoldt estimate from the already proved zeta
prime number theorem, with the elementary five-power correction retained. -/

namespace TwoPointCorrelations

open Filter

lemma modFive_constant_absorption (c : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ Real.exp (c ^ 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hsq := Real.sq_sqrt (Real.log_nonneg hx)
  have hn : 0 ≤ c ^ 2 + Real.log x - c * Real.sqrt (Real.log x) := by
    nlinarith [sq_nonneg (Real.sqrt (Real.log x) - c / 2), sq_nonneg c]
  have he : Real.exp (c ^ 2) * x * Real.exp (-c * Real.sqrt (Real.log x)) =
      Real.exp (c ^ 2 + Real.log x - c * Real.sqrt (Real.log x)) := by
    calc
      _ = Real.exp (c ^ 2) * Real.exp (Real.log x) *
          Real.exp (-c * Real.sqrt (Real.log x)) := by rw [Real.exp_log hxp]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [he]
  exact Real.one_le_exp hn

theorem modFive_zeta_psi_decay : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤
      C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, hc, hO⟩ := Erdos970.Strong_PNT
  obtain ⟨C, hC⟩ := hO.bound
  refine ⟨c, |C| + 1, hc, by positivity, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (1 : ℝ)] with x h hx
  change ‖Erdos970.ChebyshevPsi x - x‖ ≤
    C * ‖x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2))‖ at h
  rw [modFive_chebyshevPsi_eq (by linarith : 0 ≤ x), ← Real.sqrt_eq_rpow] at h
  change |Chebyshev.psi x - x| ≤ C * |x * Real.exp (-c * Real.sqrt (Real.log x))| at h
  have hp : 0 < x * Real.exp (-c * Real.sqrt (Real.log x)) :=
    mul_pos (by linarith) (Real.exp_pos _)
  rw [abs_of_pos hp] at h
  calc
    _ ≤ C * (x * Real.exp (-c * Real.sqrt (Real.log x))) := h
    _ ≤ (|C| + 1) * (x * Real.exp (-c * Real.sqrt (Real.log x))) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (by positivity)
    _ = _ := by ring

theorem modFive_principal_psi_decay : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ‖modFiveTwistedPsi 1 x - (x : ℂ)‖ ≤
      C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := modFive_zeta_psi_decay
  let K := C + (Real.log 5 + 8) * Real.exp (c ^ 2)
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  refine ⟨c, K, hc, by dsimp [K]; positivity, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with x hb hx
  have herr := modFive_principal_psi_error hx
  have hp := sqrt_mul_log_le_exp_sqrt c hx
  have hone := mul_le_mul_of_nonneg_left (modFive_constant_absorption c hx) hlog5
  have hcast : ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ = |Chebyshev.psi x - x| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ = ‖(modFiveTwistedPsi 1 x - (Chebyshev.psi x : ℂ)) +
        ((Chebyshev.psi x : ℂ) - (x : ℂ))‖ := by congr 1; ring
    _ ≤ ‖modFiveTwistedPsi 1 x - (Chebyshev.psi x : ℂ)‖ +
        ‖(Chebyshev.psi x : ℂ) - (x : ℂ)‖ := norm_add_le _ _
    _ ≤ (Real.log 5 + 2 * Real.sqrt x * Real.log x) +
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      rw [hcast]
      exact add_le_add herr hb
    _ ≤ K * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
      dsimp [K]
      nlinarith

end TwoPointCorrelations

end OAI

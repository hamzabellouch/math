import OAI.NumberTheory.DirichletL.Reflection.TerminalThreshold
import OAI.NumberTheory.DirichletL.Reflection.RamifiedWidth

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open CompletedDyadic CompletedGauss
noncomputable section

lemma fixed_abs_log_threshold (C η : ℝ) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z → |Real.logb Z C|≤η := by
  obtain ⟨Z₀,hZ₀,h⟩ := InverseTerminalWidths.constant_log_error
    (Real.exp |Real.log C|) η (Real.exp_pos _) hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ
  have hz : 0<Real.log Z := Real.log_pos (lt_of_lt_of_le hZ₀ hZ)
  have hh := h Z hZ
  simpa only [Real.logb,Real.log_exp,abs_div,abs_of_pos hz] using hh

lemma reflectedExponent_threshold_error (O₀ H S₀ B₀ za v ell el Td err η : ℝ)
    (herr : |err|≤η) :
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el (Td+err) ≤
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell el Td+η/2 := by
  have hη : 0≤η := (abs_nonneg err).trans herr
  have he : -η≤err := (abs_le.mp herr).1
  have hh : max 0 (Td-v-3*ell-el) ≤ max 0 (Td+err-v-3*ell-el)+η := by
    apply max_le
    · linarith [le_max_left (0:ℝ) (Td+err-v-3*ell-el)]
    · linarith [le_max_right (0:ℝ) (Td+err-v-3*ell-el)]
  unfold InverseTerminalWidths.reflectedExponent
  linarith

theorem literal_threshold_error_uniform (C η : ℝ) (hC : 0<C) (hη : 0<η) :
    ∃ Z₀ : ℝ, 1<Z₀ ∧ ∀ Z : ℝ, Z₀≤Z → ∀ (m : ℕ) (O₀ H S₀ B₀ za v ell Td : ℝ),
    InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
      (3*Real.logb Z (ramifiedScale 1 completedRamifiedStep m)) (Td+Real.logb Z C) ≤
      InverseTerminalWidths.reflectedExponent O₀ H S₀ B₀ za v ell
        (InverseTerminalWidths.ramifiedWidth Z m) Td+η/2 := by
  obtain ⟨Z₀,hZ₀,herr⟩ := fixed_abs_log_threshold (C/81) η hη
  refine ⟨Z₀,hZ₀,?_⟩
  intro Z hZ m O₀ H S₀ B₀ za v ell Td
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hid : Td+Real.logb Z C-4*Real.logb Z 3=Td+Real.logb Z (C/81) := by
    rw [Real.logb_div hC.ne' (by norm_num)]
    have hp := Real.logb_pow Z 3 4
    norm_num at hp
    linarith
  have hh := literal_reflectedExponent_le_signed Z hz m O₀ H S₀ B₀ za v ell (Td+Real.logb Z C)
  rw [hid] at hh
  exact hh.trans (reflectedExponent_threshold_error O₀ H S₀ B₀ za v ell
    (InverseTerminalWidths.ramifiedWidth Z m) Td (Real.logb Z (C/81)) η (herr Z hZ))

end
end SevenEighths.InverseReflectedPhase

end OAI

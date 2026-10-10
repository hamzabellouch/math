import OAI.Probability.FreeIsing.Trees.PathSums

namespace OAI

noncomputable section

namespace Problem367

theorem exists_path_cutoff_constant {a q : ℝ} (ha : 0 < a) (hq : 1 < q) (C₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ C₀ ≤ C ∧ 1 ≤ Real.log q * C ∧
      2 ≤ (a / 2) * q ^ C := by
  have hl : 0 < Real.log q := Real.log_pos hq
  let C := max C₀ (max (1 / Real.log q) (Real.log (4 / a) / Real.log q))
  have hC₀ : C₀ ≤ C := le_max_left _ _
  have hC₁ : 1 / Real.log q ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₂ : Real.log (4 / a) / Real.log q ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, (one_div_pos.mpr hl).trans_le hC₁, hC₀, ?_, ?_⟩
  · have := (div_le_iff₀ hl).mp hC₁
    nlinarith
  · have hpow : 4 / a ≤ q ^ C := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans hq)]
      calc
        4 / a = Real.exp (Real.log (4 / a)) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp (Real.log q * C) := by
          apply Real.exp_le_exp.mpr
          have := (div_le_iff₀ hl).mp hC₂
          nlinarith
    have := mul_le_mul_of_nonneg_left hpow (show 0 ≤ a / 2 by positivity)
    have heq : (a / 2) * (4 / a) = 2 := by field_simp; ring
    rwa [heq] at this

theorem path_log_cutoff_bound {a q C I : ℝ} {n : ℕ}
    (ha : 0 ≤ a) (hq : 1 < q) (hI : 1 ≤ I)
    (hC : 1 ≤ Real.log q * C) (hbase : 2 ≤ (a / 2) * q ^ C)
    (hcut : C * (1 + Real.log I) ≤ (n : ℝ)) :
    2 * I ≤ (a / 2) * q ^ n := by
  have hlq : 0 < Real.log q := Real.log_pos hq
  have hI0 : 0 < I := zero_lt_one.trans_le hI
  have hlI : 0 ≤ Real.log I := Real.log_nonneg hI
  have hexp : Real.log q * C + Real.log I ≤ Real.log q * n := by
    have h₁ := mul_le_mul_of_nonneg_left hcut hlq.le
    have h₂ := mul_le_mul_of_nonneg_right hC hlI
    nlinarith
  have hpow : q ^ C * I ≤ q ^ n := by
    calc
      q ^ C * I = Real.exp (Real.log q * C + Real.log I) := by
        rw [Real.exp_add, Real.exp_log hI0, Real.rpow_def_of_pos (zero_lt_one.trans hq)]
      _ ≤ Real.exp (Real.log q * n) := Real.exp_le_exp.mpr hexp
      _ = q ^ n := by rw [← Real.rpow_natCast, Real.rpow_def_of_pos (zero_lt_one.trans hq)]
  calc
    2 * I ≤ ((a / 2) * q ^ C) * I := mul_le_mul_of_nonneg_right hbase hI0.le
    _ = (a / 2) * (q ^ C * I) := by ring
    _ ≤ (a / 2) * q ^ n := mul_le_mul_of_nonneg_left hpow (by positivity)

def pathCutoff (C ω I : ℝ) : ℕ := Nat.ceil (C * (ω⁻¹ + Real.log I))

theorem pathCutoff_le {C ω I : ℝ} (hC : 0 ≤ C) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hI : 1 ≤ I) :
    (pathCutoff C ω I : ℝ) ≤ (C + 1) * (ω⁻¹ + Real.log I) := by
  have hωinv : 1 ≤ ω⁻¹ := (one_le_inv₀ hω).mpr hω1
  have hlI : 0 ≤ Real.log I := Real.log_nonneg hI
  have hscale : 1 ≤ ω⁻¹ + Real.log I := by linarith
  have hnonneg : 0 ≤ C * (ω⁻¹ + Real.log I) := mul_nonneg hC (by linarith)
  have hceil := Nat.ceil_lt_add_one hnonneg
  change (Nat.ceil (C * (ω⁻¹ + Real.log I)) : ℝ) ≤ _
  nlinarith

theorem pathCutoff_log_bound {C ω I : ℝ} {n : ℕ} (hC : 0 ≤ C)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hn : pathCutoff C ω I ≤ n) :
    C * (1 + Real.log I) ≤ (n : ℝ) := by
  have hωinv : 1 ≤ ω⁻¹ := (one_le_inv₀ hω).mpr hω1
  calc
    C * (1 + Real.log I) ≤ C * (ω⁻¹ + Real.log I) := by gcongr
    _ ≤ (pathCutoff C ω I : ℝ) := Nat.le_ceil _
    _ ≤ (n : ℝ) := by exact_mod_cast hn

theorem pathCutoff_absorption {V K a q C ω : ℝ} {n : ℕ}
    (hV : 0 < V) (hVK : V ≤ K) (hK : 1 ≤ K) (ha : 0 ≤ a) (hq : 1 < q)
    (hC0 : 0 ≤ C) (hC : 1 ≤ Real.log q * C)
    (hbase : 2 ≤ (a / 2) * q ^ C) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : pathCutoff C ω (1 + Real.log (K / V)) ≤ n) :
    Real.exp (-a * q ^ n) ≤ V ^ 2 * Real.exp (-(a / 2) * q ^ n) := by
  have hI : 1 ≤ 1 + Real.log (K / V) := by
    have hratio : 1 ≤ K / V := (one_le_div hV).mpr hVK
    have := Real.log_nonneg hratio
    linarith
  apply superexponential_path_absorption hV hK
  apply path_log_cutoff_bound ha hq hI hC hbase
  exact pathCutoff_log_bound hC0 hω hω1 hn

end Problem367

end

end OAI

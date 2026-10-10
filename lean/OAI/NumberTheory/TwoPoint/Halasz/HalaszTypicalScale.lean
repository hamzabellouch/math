import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalMean

namespace OAI

/-! The cutoff above the typical bands costs a power of log N and keeps
the central distance saving. -/

namespace TwoPointCorrelations

open Filter

lemma halasz_typical_decay {M : ℝ} (_hM : 0 ≤ M) :
    (M+1)*Real.exp (-M/2)  ≤  10*Real.exp (-2*M/5) := by
  have hh := Real.add_one_le_exp (M/10)
  have hm : M+1  ≤  10*Real.exp (M/10) := by linarith
  calc
    _  ≤  (10*Real.exp (M/10))*Real.exp (-M/2) :=
      mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc,←Real.exp_add]
      rw [show M/10 + -M/2 = -2*M/5 by ring]

lemma halasz_typical_cutoff_scale :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.exp (Real.sqrt (Real.log (N:ℝ))) ∧
      Real.log (N:ℝ)^16 ≤ Real.exp (Real.sqrt (Real.log (N:ℝ))) ∧
      Real.exp (Real.sqrt (Real.log (N:ℝ))) ≤ (N:ℝ)/2 ∧
      (1+Real.log (Real.exp (Real.sqrt (Real.log (N:ℝ)))))*
        Real.log (Real.log N)/Real.log N  ≤  (Real.log N)^(-1/4:ℝ) := by
  have hl : Tendsto (fun N:ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1/4 by norm_num)).bound
    (show (0:ℝ) < 1/32 by norm_num)
  filter_upwards [hl.eventually hsmall,
    hl.eventually (eventually_ge_atTop (max 16 (4*Real.log 2))),
    eventually_ge_atTop 2] with N hsmall hL hN
  let L := Real.log (N:ℝ)
  have hL16 : 16 ≤ L := (le_max_left _ _).trans hL
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL1
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hp : 0 ≤ L^(1/4:ℝ) := Real.rpow_nonneg hL0.le _
  rw [Real.norm_eq_abs,abs_of_nonneg hlog,Real.norm_eq_abs,
    abs_of_nonneg hp] at hsmall
  have hquarter : L^(1/4:ℝ) ≤ Real.sqrt L := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hroot : Real.sqrt L ≤ L/2 := by
    nlinarith [Real.sq_sqrt hL0.le,Real.sqrt_nonneg L]
  refine ⟨Real.one_le_exp (Real.sqrt_nonneg _),?_,?_,?_⟩
  · have hpos : 0 < L^16 := pow_pos hL0 16
    rw [←Real.exp_log hpos]
    apply Real.exp_le_exp.mpr
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    dsimp [L] at hquarter hsmall ⊢
    linarith
  · apply (le_div_iff₀ (show (0:ℝ) < 2 by norm_num)).mpr
    change Real.exp (Real.sqrt L)*2 ≤ (N:ℝ)
    have hlog2 : 4*Real.log 2 ≤ L := (le_max_right _ _).trans hL
    calc
      _ = Real.exp (Real.sqrt L+Real.log 2) := by
        rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
      _ ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hN0
  · rw [Real.log_exp]
    change (1+Real.sqrt L)*Real.log L/L ≤ L^(-1/4:ℝ)
    calc
      _  ≤  (2*Real.sqrt L)*((1/2:ℝ)*L^(1/4:ℝ))/L := by
        apply div_le_div_of_nonneg_right _ hL0.le
        apply mul_le_mul
        · linarith
        · linarith
        · exact hlog
        · positivity
      _ = L^(-1/4:ℝ) := by
        rw [Real.sqrt_eq_rpow]
        have he : L^(1/2:ℝ)*L^(1/4:ℝ)/L=L^(-1/4:ℝ) := by
          rw [←Real.rpow_add hL0]
          calc
            _ = L^((1/2:ℝ)+1/4)/L^(1:ℝ) := by rw [Real.rpow_one]
            _ = L^((1/2:ℝ)+1/4-1) := (Real.rpow_sub hL0 _ _).symm
            _ = _ := by norm_num
        convert he using 1
        ring

end TwoPointCorrelations

end OAI

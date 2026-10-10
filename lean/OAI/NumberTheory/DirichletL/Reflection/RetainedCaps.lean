import OAI.NumberTheory.DirichletL.Reflection.RetainedWidth

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve
noncomputable section

lemma retained_shell_le_ratio (scale T : ℝ) (hs : 0<scale)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*T)) :
    (2:ℝ)^i.2.2≤16*T/scale ∧ (2:ℝ)^i.2.1≤16*T/scale := by
  have hh := (mem_retainedDyads _ _ hs i).mp hi
  have hl := rawDyadicCenter_pow_lower scale hs.le i
  have hp : (2:ℝ)^(i.1+i.2.2+3*i.2.1)≤16*T/scale := by
    exact (le_div_iff₀ hs).mpr (by nlinarith)
  constructor
  · exact (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show i.2.2 ≤ i.1 + i.2.2 + 3 * i.2.1 by omega)).trans hp
  · exact (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show i.2.1 ≤ i.1 + i.2.2 + 3 * i.2.1 by omega)).trans hp

lemma retained_shell_log_cap (scale Z δ Lcap η : ℝ) (hs : 0<scale) (hZ : 1<Z)
    (hscale : scale⁻¹≤Z^Lcap) (hconst : Real.logb Z 16≤η)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*Z^δ)) :
    Real.logb Z ((2:ℝ)^i.2.2)≤δ+Lcap+η ∧
    Real.logb Z ((2:ℝ)^i.2.1)≤δ+Lcap+η := by
  have hz := lt_trans zero_lt_one hZ
  have hb : 16*Z^δ/scale≤16*Z^(δ+Lcap) := by
    rw [Real.rpow_add hz,div_eq_mul_inv,←mul_assoc]
    exact mul_le_mul_of_nonneg_left hscale (by positivity)
  have hshell := retained_shell_le_ratio scale (Z^δ) hs i hi
  have hlog (n : ℕ) (hn : (2:ℝ)^n≤16*Z^(δ+Lcap)) :
      Real.logb Z ((2:ℝ)^n)≤δ+Lcap+η := by
    have hh := Real.logb_le_logb_of_le hZ (by positivity : (0:ℝ)<2^n) hn
    rw [Real.logb_mul (by norm_num : (16:ℝ)≠0) (Real.rpow_pos_of_pos hz _).ne',
      Real.logb_rpow hz (ne_of_gt hZ)] at hh
    linarith
  exact ⟨hlog _ (hshell.1.trans hb),hlog _ (hshell.2.trans hb)⟩

lemma extracted_log_le_shell (Z Q : ℝ) (hZ : 1<Z) (hQ : 0<Q)
    (I : Ideal ActualEisensteinCubic.O) (hI : I≠0) :
    Real.logb Z (Q/Ideal.absNorm I)≤Real.logb Z Q := by
  have hn : (1:ℝ)≤Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  apply Real.logb_le_logb_of_le hZ (div_pos hQ (lt_of_lt_of_le zero_lt_one hn))
  exact div_le_self hQ.le hn

lemma retained_extracted_log_budget (scale Z δ Lscale Lrow Lslot η X L : ℝ)
    (hs : 0<scale) (hZ : 1<Z) (hX : 0<X) (hL : 0<L)
    (hscale : scale⁻¹≤Z^Lscale) (hconst : Real.logb Z 16≤η)
    (hrow : X≤Z^Lrow) (hslot : L≤Z^Lslot)
    (i : ℕ×ℕ×ℕ) (hi : i∈retainedDyads scale (16*Z^δ))
    (D1 D2 : Ideal ActualEisensteinCubic.O) (h1 : D1≠0) (h2 : D2≠0) :
    Real.logb Z X+Real.logb Z (((2:ℝ)^i.2.2)/Ideal.absNorm D1)+
      Real.logb Z (((2:ℝ)^i.2.1)/Ideal.absNorm D2)+Real.logb Z L≤
        Lrow+Lslot+2*(δ+Lscale+η) := by
  have hz := lt_trans zero_lt_one hZ
  have hr := Real.logb_le_logb_of_le hZ hX hrow
  have hl := Real.logb_le_logb_of_le hZ hL hslot
  rw [Real.logb_rpow hz (ne_of_gt hZ)] at hr hl
  obtain ⟨hn,hb⟩ := retained_shell_log_cap scale Z δ Lscale η hs hZ hscale hconst i hi
  have hn' := extracted_log_le_shell Z ((2:ℝ)^i.2.2) hZ (by positivity) D1 h1
  have hb' := extracted_log_le_shell Z ((2:ℝ)^i.2.1) hZ (by positivity) D2 h2
  linarith
end
end SevenEighths.InverseReflectedPhase

end OAI

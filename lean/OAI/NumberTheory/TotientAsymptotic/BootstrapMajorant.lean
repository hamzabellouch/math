import OAI.NumberTheory.TotientAsymptotic.BootstrapIndex

namespace OAI

/-! A concrete logarithmic majorant for the counting recurrence. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

def bootstrapHeight (J : ℕ) : ℝ := 1+Real.log ((J:ℝ)+1)
def bootstrapMajorant (J : ℕ) : ℝ := Real.exp (9*(Real.log (bootstrapHeight J))^2)

lemma bootstrapHeight_one_le (J : ℕ) : 1 ≤ bootstrapHeight J := by
  have hh := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) J; linarith : (1:ℝ) ≤ (J:ℝ)+1)
  dsimp [bootstrapHeight]
  linarith

lemma bootstrapHeight_mono : Monotone bootstrapHeight := by
  intro I J hIJ
  change 1+Real.log ((I:ℝ)+1) ≤ 1+Real.log ((J:ℝ)+1)
  have hh : (I:ℝ) ≤ J := Nat.cast_le.mpr hIJ
  have hle : (I:ℝ)+1 ≤ (J:ℝ)+1 := by linarith
  have ht := Real.log_le_log (by positivity : 0 < (I:ℝ)+1) hle
  linarith

lemma bootstrapMajorant_one_le (J : ℕ) : 1 ≤ bootstrapMajorant J := Real.one_le_exp (by positivity)

lemma bootstrapMajorant_mono : Monotone bootstrapMajorant := by
  intro I J hIJ
  apply Real.exp_le_exp.mpr
  have hI : 0 ≤ Real.log (bootstrapHeight I) := Real.log_nonneg (bootstrapHeight_one_le I)
  have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one (bootstrapHeight_one_le I)) (bootstrapHeight_mono hIJ)
  nlinarith

lemma bootstrapHeight_tendsto : Tendsto bootstrapHeight atTop atTop := by
  have hi : Tendsto (fun J : ℕ => (J:ℝ)+1) atTop atTop :=
    by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (b-1))] with J hJ
      linarith
  exact tendsto_atTop_add_const_left _ 1 (Real.tendsto_log_atTop.comp hi)

lemma majorant_real_drop {b c : ℝ} (hc : 1 ≤ c) (hcb : c ≤ (83/100:ℝ)*b)
    (hlog : 5 ≤ Real.log b) :
    Real.exp (9*(Real.log c)^2)*b^3 ≤ Real.exp (9*(Real.log b)^2) := by
  have hb : 0 < b := by nlinarith
  have hc0 : 0 < c := by linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hh := Real.log_le_log hc0 hcb
  rw [Real.log_mul (by norm_num : (83/100:ℝ)≠0) hb.ne'] at hh
  have hr : Real.log (83/100:ℝ) ≤ -(17/100:ℝ) := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<83/100)
    linarith
  have hs : (Real.log c)^2 ≤ (Real.log b-17/100)^2 := by nlinarith
  have he : 9*(Real.log c)^2+3*Real.log b ≤ 9*(Real.log b)^2 := by nlinarith
  have hp : b^3=Real.exp (3*Real.log b) := by
    simpa only [Nat.cast_ofNat,Real.exp_log hb] using (Real.exp_nat_mul (Real.log b) 3).symm
  rw [hp,← Real.exp_add]
  exact Real.exp_le_exp.mpr he

lemma bootstrap_majorant_contraction (A : ℝ) : ∀ᶠ J : ℕ in atTop,
    A*(1+Real.log J)^2*bootstrapMajorant (bootstrapIndex J) ≤ bootstrapMajorant J/4 := by
  have hlarge : ∀ᶠ J : ℕ in atTop,100*(1+Real.log 2) ≤ Real.log (J:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hpow : ∀ᶠ J : ℕ in atTop,4*max A 0 ≤ bootstrapHeight J :=
    bootstrapHeight_tendsto.eventually (eventually_ge_atTop _)
  filter_upwards [bootstrap_index_bounds,hlarge,hpow,
    (Real.tendsto_log_atTop.comp bootstrapHeight_tendsto).eventually (eventually_ge_atTop (5:ℝ))] with J hidx hlarge hpow hlog
  obtain ⟨hK,hKJ,hLK,_⟩ := hidx
  have hJ : 0 < J := by omega
  have hJ0 : (0:ℝ) < J := by exact_mod_cast hJ
  have hK0 : (0:ℝ) < bootstrapIndex J := by exact_mod_cast (show 0 < bootstrapIndex J by omega)
  have hheight : bootstrapHeight (bootstrapIndex J) ≤ (83/100:ℝ)*bootstrapHeight J := by
    have hkplus : (bootstrapIndex J:ℝ)+1 ≤ 2*bootstrapIndex J := by
      have hh : (1:ℝ) ≤ bootstrapIndex J := by exact_mod_cast hK
      linarith
    have hl := Real.log_le_log (by positivity : 0 < (bootstrapIndex J:ℝ)+1) hkplus
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hK0.ne'] at hl
    have hjplus := Real.log_le_log hJ0 (by linarith : (J:ℝ) ≤ (J:ℝ)+1)
    dsimp [bootstrapHeight]
    linarith
  have hdrop := majorant_real_drop (bootstrapHeight_one_le _) hheight hlog
  have hb := bootstrapHeight_one_le J
  have hB : 0 < bootstrapHeight J := by linarith
  have hln : 0 ≤ 1+Real.log (J:ℝ) := by
    have hh : 0 ≤ Real.log (J:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ J by omega))
    linarith
  have hhl : 1+Real.log (J:ℝ) ≤ bootstrapHeight J := by
    have hj : (J:ℝ) ≤ (J:ℝ)+1 := by linarith
    dsimp [bootstrapHeight]
    linarith [Real.log_le_log hJ0 hj]
  have hcoeff : 4*A*(1+Real.log J)^2 ≤ (bootstrapHeight J)^3 := by
    have hs : (1+Real.log (J:ℝ))^2 ≤ (bootstrapHeight J)^2 := by nlinarith
    have hA : A ≤ max A 0 := le_max_left _ _
    have hA0 : 0 ≤ max A 0 := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hs hA0,
      mul_le_mul_of_nonneg_right hpow (sq_nonneg (bootstrapHeight J))]
  have hG : 0 ≤ bootstrapMajorant (bootstrapIndex J) := (Real.exp_pos _).le
  change bootstrapMajorant (bootstrapIndex J)*(bootstrapHeight J)^3 ≤ bootstrapMajorant J at hdrop
  nlinarith [mul_le_mul_of_nonneg_right hcoeff hG]

end TotientAsymptotic

end

end OAI

import OAI.NumberTheory.Jacobsthal.Estimates.PatternCardGrowth
import OAI.NumberTheory.Jacobsthal.Estimates.SourceExtensionScale

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


open _root_.Filter
namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosLargeHeightBlocks
  ErdosInversePrimeBin ErdosInverseBoxHeight ErdosInverseEuler

theorem normalization_budgets (xi eps : ℝ) (hxi : 0 < xi) (heps : 0 < eps) :
    ∀ᶠ R : ℝ in atTop,1 < R ∧ Real.log R ≤ R^((1 : ℝ)/40) ∧
      16 ≤ eps*xi*R^((1 : ℝ)/20) := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by norm_num : (0 : ℝ) < 1/40)).bound zero_lt_one
  filter_upwards [hlog,(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/20)).eventually_ge_atTop (16/(eps*xi)),
    eventually_gt_atTop (1 : ℝ)] with R hlog hc hR
  have hR0 : 0 < R := by linarith
  refine ⟨hR,?_,?_⟩
  · simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (Real.log_pos hR).le,
      abs_of_nonneg (Real.rpow_nonneg hR0.le _),one_mul] using hlog
  · have hh := (div_le_iff₀ (mul_pos heps hxi)).mp hc
    nlinarith

theorem source_pattern_error_normalized (alpha xi eps : ℝ)
    (halpha : 0 < alpha) (hxi : 0 < xi) (hxi1 : xi ≤ 1) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop,∀ (R theta : ℝ),z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
      ∀ (H : ℕ) (C0 : ℤ),0 < H →
        max (H : ℝ) (|(C0 : ℝ)|/R)/(H : ℝ) ≤ (sourceZ z)^12 →
        ((blockCount C0 R theta H : ℝ)*
          (patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H) : ℝ)*R^((9 : ℝ)/10))/
            ((primeBin R theta).card : ℝ) ≤ eps := by
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (normalization_budgets xi eps hxi heps)
  filter_upwards [source_model_population alpha xi halpha hxi hxi1,source_patternCard_Z,
    source_Z_power_R alpha (1/40) 14 halpha (by norm_num) (by decide),
    sourceZ_tendsto_atTop.eventually_ge_atTop 2,(tendsto_rpow_atTop halpha).eventually_ge_atTop R0]
    with z hpop hM hZpow hZ hzR
  intro R theta hRlo hthetal hthetau H C0 hH hratio
  have hp := hpop R theta hRlo hthetal hthetau
  have hb := hR0 R (hzR.trans hRlo)
  have hR : 0 < R := by linarith [hp.1]
  have hlog : 0 < Real.log R := Real.log_pos hp.1
  have htheta : 0 ≤ theta := (by positivity : (0 : ℝ) ≤ xi/4).trans hthetal
  let n : ℝ := blockCount C0 R theta H
  let M : ℝ := patternCard (divisorModulus (sourceW z) H) (coprimeModulus (sourceW z) H)
  have hn : n ≤ (sourceZ z)^13 := blockCount_source_bound C0 R theta (sourceZ z) H
    hR htheta (hthetau.trans hxi1) hH hZ hratio
  have hMZ : M ≤ sourceZ z := hM H
  have hnM : n*M ≤ R^((1 : ℝ)/40) := by
    calc
      _ ≤ (sourceZ z)^13*sourceZ z := mul_le_mul hn hMZ (Nat.cast_nonneg _) (by positivity)
      _ = (sourceZ z)^14 := by ring
      _ ≤ _ := hZpow.2 R hRlo
  have hprod : (n*M*R^((9 : ℝ)/10))*(16*Real.log R) ≤ 16*R^((19 : ℝ)/20) := by
    have hpair := mul_le_mul hnM hb.2.1 hlog.le (Real.rpow_nonneg hR.le _)
    have hm := mul_le_mul_of_nonneg_left hpair (show 0 ≤ 16*R^((9 : ℝ)/10) by positivity)
    calc
      _ ≤ 16*R^((9 : ℝ)/10)*(R^((1 : ℝ)/40)*R^((1 : ℝ)/40)) := by nlinarith
      _ = 16*(R^((9 : ℝ)/10)*(R^((1 : ℝ)/40)*R^((1 : ℝ)/40))) := by ring
      _ = _ := by rw [← Real.rpow_add hR,← Real.rpow_add hR];norm_num
  have htarget : 16*R^((19 : ℝ)/20) ≤ eps*xi*R := by
    have hh := mul_le_mul_of_nonneg_right hb.2.2 (Real.rpow_nonneg hR.le ((19 : ℝ)/20))
    calc
      _ ≤ (eps*xi*R^((1 : ℝ)/20))*R^((19 : ℝ)/20) := hh
      _ = _ := by rw [mul_assoc (eps*xi),← Real.rpow_add hR];norm_num
  have herr : n*M*R^((9 : ℝ)/10) ≤ eps*(xi*R/(16*Real.log R)) := by
    have hh := (le_div_iff₀ (show 0 < 16*Real.log R by positivity)).mpr (hprod.trans htarget)
    have he : eps*(xi*R/(16*Real.log R)) = eps*xi*R/(16*Real.log R) := by ring
    exact hh.trans_eq he.symm
  have hlow : 0 < xi*R/(16*Real.log R) := by positivity
  have hPC : 0 < ((primeBin R theta).card : ℝ) := hlow.trans_le hp.2.2
  apply (div_le_iff₀ hPC).mpr
  exact herr.trans (mul_le_mul_of_nonneg_left hp.2.2 heps.le)

end ErdosVarianceLargeMap


end Erdos970

end OAI

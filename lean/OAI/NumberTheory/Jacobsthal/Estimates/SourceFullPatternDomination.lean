import OAI.NumberTheory.Jacobsthal.Analysis.PatternErrorNormalization

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


open _root_.Filter
namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosLargeHeightBlocks ErdosInversePrimeBin
  ErdosInverseBoxHeight ErdosInverseEuler
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem source_full_pattern_domination (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ xi : ℝ,0 < xi → xi ≤ 1 → ∀ eps : ℝ,0 < eps →
      ∀ᶠ z : ℝ in atTop,1 < z ∧
      ∀ (R theta : ℝ),z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
      ∀ (H : ℕ) (C0 : ℤ),2 ≤ H → Int.gcd C0 (H : ℤ) = 1 →
        R^((4 : ℝ)/5) ≤ (H : ℝ) → (H : ℝ) ≤ R*(sourceZ z)^11 →
        max (H : ℝ) (|(C0 : ℝ)|/R)/(H : ℝ) ≤ (sourceZ z)^12 →
      ∃ (hw : 0 ≤ sourceW z) (hP : ∀ p ∈ primeBin R theta,p.Prime)
        (hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ)),
      ∀ E : ErdosLargePatternLaw.FullPattern (sourceW z) H → Prop,
        ((fullPrimeEvent (primeBin R theta) (sourceW z) H C0 hw hP hlarge E).card : ℝ)/
          ((primeBin R theta).card : ℝ) ≤ C*patternEventWeight (sourceW z) H E+eps := by
  obtain ⟨C,hC,hcount⟩ := source_full_event_count alpha halpha
  refine ⟨16*C,by positivity,?_⟩
  intro xi hxi hxi1 eps heps
  filter_upwards [hcount,source_pattern_error_normalized alpha xi eps halpha hxi hxi1 heps,
    source_model_population alpha xi halpha hxi hxi1,sourceW_tendsto_atTop.eventually_ge_atTop 0]
    with z hzcount hzerror hzpop hw
  refine ⟨hzcount.1,?_⟩
  intro R theta hRlo hthetal hthetau H C0 hH hC0 hHlo hHhi hratio
  have hpop := hzpop R theta hRlo hthetal hthetau
  have hR : 0 < R := by linarith [hpop.1]
  have hlog : 0 < Real.log R := Real.log_pos hpop.1
  have htheta : 0 < theta := (by positivity : (0 : ℝ) < xi/4).trans_le hthetal
  have htheta1 := hthetau.trans hxi1
  have hP : ∀ p ∈ primeBin R theta,p.Prime := fun p hp => ((mem_primeBin hR.le htheta.le p).mp hp).1
  have hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ) := fun p hp =>
    hpop.2.1.trans_lt ((mem_primeBin hR.le htheta.le p).mp hp).2.1
  refine ⟨hw,hP,hlarge,?_⟩
  intro E
  have hc := hzcount.2 R theta hRlo htheta htheta1 H C0 hH hC0 hHlo hHhi hw hP hlarge E
  have he := hzerror R theta hRlo hthetal hthetau H C0 (by omega) hratio
  have hlow : 0 < xi*R/(16*Real.log R) := by positivity
  have hPC : 0 < ((primeBin R theta).card : ℝ) := hlow.trans_le hpop.2.2
  have hcoef : C*theta*R/Real.log R ≤ (16*C)*((primeBin R theta).card : ℝ) := by
    apply (div_le_iff₀ hlog).mpr
    have hb := (div_le_iff₀ (show 0 < 16*Real.log R by positivity)).mp hpop.2.2
    have hm := mul_le_mul_of_nonneg_left hb hC.le
    have ht := mul_le_mul_of_nonneg_left hthetau (show 0 ≤ C*R by positivity)
    nlinarith only [hm,ht]
  have hmain : (C*theta*R/Real.log R*patternEventWeight (sourceW z) H E)/
      ((primeBin R theta).card : ℝ) ≤ (16*C)*patternEventWeight (sourceW z) H E := by
    apply (div_le_iff₀ hPC).mpr
    have hh := mul_le_mul_of_nonneg_right hcoef (patternEventWeight_nonneg (sourceW z) H E)
    nlinarith only [hh]
  have hd := div_le_div_of_nonneg_right hc hPC.le
  rw [add_div] at hd
  exact hd.trans (add_le_add hmain he)

end ErdosVarianceLargeMap


end Erdos970

end OAI

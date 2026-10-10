import OAI.MeasureTheory.SelfSimilar.EntropyGap

namespace OAI

universe uι

namespace EntropyRateDimension
open MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal

theorem exists_slightly_larger_depth {d χ h : ℝ} (hd : 0 ≤ d) (hgap : d*χ < h) :
    ∃ a : ℝ, χ < a ∧ d*a < h := by
  let t := (h-d*χ)/(2*(d+1))
  have hp : 0 < 2*(d+1) := by linarith
  have ht : 0 < t := div_pos (sub_pos.mpr hgap) hp
  have he : t*(2*(d+1))=h-d*χ := div_mul_cancel₀ _ hp.ne'
  refine ⟨χ+t,by linarith,?_⟩
  nlinarith

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
local instance : MeasurableSpace ι := ⊤
local instance : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩

theorem exponent_lower_bound (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) : min 1 (S.entropyRate/S.lyapunov) ≤ Coding.exponent S := by
  classical
  by_contra! hstrict
  obtain ⟨d,hed,hdm⟩ := exists_between hstrict
  have hd : 0 ≤ d := (Coding.exponent_nonneg S).trans hed.le
  have hd1 : d < 1 := hdm.trans_le (min_le_left _ _)
  have hdr : d < S.entropyRate/S.lyapunov := hdm.trans_le (min_le_right _ _)
  have hdh : d*S.lyapunov < S.entropyRate := (lt_div_iff₀ S.lyapunov_pos).mp hdr
  obtain ⟨a,hχa,hda⟩ := exists_slightly_larger_depth hd hdh
  have hap : 0 < a := S.lyapunov_pos.trans hχa
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hε : 0 < (S.entropyRate-d*a)*Real.log 2 := mul_pos (sub_pos.mpr hda) hl
  obtain ⟨b,hb,hbtype⟩ := exists_nat_log_small hε (Fintype.card ι)
  have hbR : (0 : ℝ)<b := by exact_mod_cast hb
  have htype : Real.log (Fintype.card (ι → Fin (b+1)))=
      (Fintype.card ι : ℝ)*Real.log ((b : ℝ)+1) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow,Nat.cast_add,Nat.cast_one]
  have hblock : (b : ℝ)*S.entropyRate ≤ (S.blocks hb).entropyRate := S.blocks_entropyRate_lower hb
  have hgap : d*((b : ℝ)*a)*Real.log 2 < (S.blocks hb).entropyRate*Real.log 2-
      Real.log (Fintype.card (ι → Fin (b+1))) := by
    rw [htype]
    have hh := mul_le_mul_of_nonneg_right hblock hl.le
    nlinarith
  obtain ⟨C,hC⟩ := S.selfSimilar_entropy_bound μ hμ hed
  apply Typed.no_strict_entropy_gap (S.blocks hb) (wordType (ι := ι)) (S.ratio_wordType hb)
    μ (S.selfSimilar_blocks μ hμ hb) hd hd1 (mul_pos hbR hap)
    (A' := (b : ℝ)*((S.lyapunov+a)/2)) _ _ hC hgap
  · rw [S.blocks_lyapunov]
    exact mul_lt_mul_of_pos_left (by linarith) hbR
  · exact mul_lt_mul_of_pos_left (by linarith) hbR

end System

theorem entropy_rate_dimension {ι : Type uι} [Fintype ι] [Nonempty ι]
    (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    lowerHausdorffDimension μ = ENNReal.ofReal (min 1 (S.entropyRate / S.lyapunov)) := by
  rw [S.selfSimilar_dimension μ hμ]
  congr 1
  exact le_antisymm (le_min (S.exponent_le_one μ hμ) (S.exponent_le_rate μ hμ)) (S.exponent_lower_bound μ hμ)

end EntropyRateDimension

end OAI

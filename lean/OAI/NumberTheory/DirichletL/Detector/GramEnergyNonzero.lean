import OAI.NumberTheory.DirichletL.Detector.GramFrequencyConvergence
import OAI.NumberTheory.DirichletL.Detector.GramNonzeroFrequency
import OAI.NumberTheory.DirichletL.Detector.LowGramDiagonal

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT RayFourExpansion
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

lemma original_pair_zero_split (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    (∑'h : O,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (-h)*
      paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) 0*paperRadialFourier U 0+
      ∑'h : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (-h.val)*
        paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  have hs := actual_correlation_radial_summable I J (-1) (by norm_num) U Q hQ
  simp only [neg_one_mul,map_neg,norm_neg] at hs
  have hh := hs.tsum_eq_add_tsum_ite 0
  simpa only [neg_zero,map_zero,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_div,nonzero_tsum_indicator] using hh

theorem original_energy_nonzero (C : CalibrationData) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    gaussEnergy (lowGaussColumns W hW Y hY) (fun I=>primaryGenerator I.val)
      (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
      (lowGaussColumn C W Y σ v) U Q=
      lowGramZeroMode C W hW Y hY σ v U Q+
      ((Q/Y^3:ℝ):ℂ)*∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,
        ((lowGramCoefficient C σ I*lowGramProfile W v ((Ideal.absNorm I.val:ℝ)/Y))*
          star (lowGramCoefficient C σ J*lowGramProfile W v ((Ideal.absNorm J.val:ℝ)/Y)))*
        ∑'h : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
          ((supported_span_primaryGenerator_iff _).mpr I.property)
          ((supported_span_primaryGenerator_iff _).mpr J.property) (-h.val)*
          paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  rw [lowGram_source_poisson C W hW Y hY σ v U Q hQ,lowGramZeroMode_eq_source]
  simp_rw [original_pair_zero_split _ _ U Q hQ,mul_add,Finset.sum_add_distrib]
  simp only [mul_add]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  ring

end SevenEighths.ProbeGramCommon
end

end OAI

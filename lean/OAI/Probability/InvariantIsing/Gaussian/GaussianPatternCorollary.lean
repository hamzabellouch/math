import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternGroundLimit
import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternNorms
import OAI.Probability.InvariantIsing.Pressure.RandomSqrtLimit

namespace OAI

/-! The Gaussian-pattern maximum-norm and minimum-spin-sum limits. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
universe u
namespace InvariantIsing

theorem gaussianPattern_norm_limits
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    (α : ℝ) (hα : 0 < α) (hmp : MarchenkoPasturInput.{u} α hα)
    (hds : DavidsonSzarekInput.{u} α hα)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : (N : ℕ) → Ω → EuclideanSpace ℝ (Fin N × Fin (gaussianPatternCount α N)))
    (hZ : ∀ N, Measurable (Z N)) (hlaw : ∀ N, HasLaw (Z N) (stdGaussian _) P) :
    ∃ eplus eminus : ℝ, 0 ≤ eplus ∧ eminus ≤ 0 ∧
      Tendsto (fun β => gaussianPatternLimit α β/β) atTop (𝓝 eplus) ∧
      Tendsto (fun β => gaussianPatternLimit α (-β)/β) atTop (𝓝 eminus) ∧
      (TendstoInMeasure P (fun k ω => ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1)) atTop
        (fun _ => Real.sqrt (2*eplus)) ∧
       Tendsto (fun k => eLpNorm (fun ω => ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1)-
        Real.sqrt (2*eplus)) 1 P) atTop (𝓝 0)) ∧
      (TendstoInMeasure P (fun k ω =>
        (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1))
        atTop (fun _ => Real.sqrt (-2*eminus)) ∧
       Tendsto (fun k => eLpNorm (fun ω =>
        (Finset.univ.inf' Finset.univ_nonempty (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1)-
          Real.sqrt (-2*eminus)) 1 P) atTop (𝓝 0)) := by
  obtain ⟨ep,hpp,hpL1,hpmean,hpt⟩ := gaussianPattern_ground_limit
    hhaar hgauss hpub α hα hmp hds P Z hZ hlaw 1
  obtain ⟨em,hmpb,hmL1,hmmean,hmt⟩ := gaussianPattern_ground_limit
    hhaar hgauss hpub α hα hmp hds P Z hZ hlaw (-1)
  have hp0 : 0 ≤ ep := le_of_tendsto_of_tendsto tendsto_const_nhds hpmean
    (Filter.Eventually.of_forall fun k => integral_nonneg fun ω =>
      gaussianPatternGroundEnergy_nonneg 1 zero_le_one _)
  have hm0 : em ≤ 0 := le_of_tendsto_of_tendsto hmmean tendsto_const_nhds
    (Filter.Eventually.of_forall fun k => integral_nonpos fun ω =>
      gaussianPatternGroundEnergy_nonpos (-1) (by norm_num) _)
  have hp := random_sqrt_scaled_limit P _ ep 2 (by norm_num)
    (fun k => (measurable_gaussianPatternGroundEnergy _ _ 1).comp (hZ (k+1)))
    (gaussianPattern_ground_uniformIntegrable α hα hds P Z hZ hlaw 1) hpp
  have hm := random_sqrt_scaled_limit P _ em (-2) (by norm_num)
    (fun k => (measurable_gaussianPatternGroundEnergy _ _ (-1)).comp (hZ (k+1)))
    (gaussianPattern_ground_uniformIntegrable α hα hds P Z hZ hlaw (-1)) hmpb
  have heqplus (k : ℕ) (ω : Ω) : Real.sqrt (2*gaussianPatternGroundEnergy 1 (Z (k+1) ω))=
      ‖gaussianPatternOperator (Z (k+1) ω)‖/(k+1) := by
    simpa only [Nat.cast_succ] using
      gaussianPattern_max_sqrt (Nat.succ_pos k) (Z (k+1) ω)
  have heqminus (k : ℕ) (ω : Ω) : Real.sqrt (-2*gaussianPatternGroundEnergy (-1) (Z (k+1) ω))=
      (Finset.univ.inf' Finset.univ_nonempty
        (fun σ : Spin (k+1) => ‖gaussianPatternSum (Z (k+1) ω) σ‖))/(k+1) := by
    simpa only [Nat.cast_succ] using
      gaussianPattern_min_sqrt (Nat.succ_pos k) (Z (k+1) ω)
  simp only [Function.comp_apply,heqplus] at hp
  simp only [Function.comp_apply,heqminus] at hm
  refine ⟨ep,em,hp0,hm0,?_,?_,hp,hm⟩
  · simpa only [one_mul] using hpt
  · simpa only [neg_one_mul] using hmt

end InvariantIsing

end

end OAI

import OAI.Analysis.FiniteFactor.Sampling.FirstDiscrepancy
import OAI.Analysis.FiniteFactor.Sampling.OrientedMoments

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- The triangular second orientation has one reflected interval of phases. -/
theorem samplingSecondTriangular_interval (h α : ℝ) (G : Set ℝ) (a c s t : ℝ)
    (hs : s ∈ Set.Ico (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    samplingOrientedWeight true true h α (Set.Icc a c) G s t =
      (Set.Ioc 0 s ∩ Set.Icc (s-c) (s-a)).indicator (fun _ => if s ∈ G then (1 : ℝ) else 0) t := by
  by_cases hts : t ≤ s
  · have hf : Int.fract (s-t) = s-t := Int.fract_eq_self.mpr ⟨by linarith,by linarith [hs.2,ht.1]⟩
    simp only [samplingOrientedWeight,ite_true,samplingWeight,hf,
      Set.indicator,Set.mem_inter_iff,Set.mem_Ioc,Set.mem_Icc]
    split_ifs <;> simp_all <;> grind
  · have hst : s-t < 0 := by linarith
    have hfloor : ⌊s-t⌋ = (-1 : ℤ) := Int.floor_eq_iff.mpr
      ⟨by norm_num; linarith [hs.1,ht.2],by norm_num; linarith⟩
    have hf : Int.fract (s-t) = s-t+1 := by rw [Int.fract,hfloor]; norm_num
    simp only [samplingOrientedWeight,ite_true,samplingWeight,hf,
      Set.indicator,Set.mem_inter_iff,Set.mem_Ioc,Set.mem_Icc]
    split_ifs <;> simp_all
    grind

/-- Reflection identifies the actual triangular second weight with a first
weight. This equality concerns values; it introduces no new random law. -/
theorem samplingSecondTriangular_reflect (h α : ℝ) (G : Set ℝ) (a c s t : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ico (0 : ℝ) 1) (hts : t ≠ s) :
    samplingOrientedWeight true true h α (Set.Icc a c) G s t =
      samplingTestedFirstWeight true h α (if s ∈ G then Set.univ else ∅)
        (Set.Icc (1-c) (1-a)) (1-s) t := by
  rw [samplingSecondTriangular_interval h α G a c s t ⟨hs.1.le,hs.2⟩ ht,
    samplingTestedFirstWeight_interval true h α (if s ∈ G then Set.univ else ∅)
      (1-c) (1-a) (1-s) t hh hh1 hα ⟨by linarith [hs.2],by linarith [hs.1]⟩]
  have h1 : 1-(1-s) = s := by ring
  have h2 : (1-c)-(1-s) = s-c := by ring
  have h3 : (1-a)-(1-s) = s-a := by ring
  simp only [samplingFirstLength,samplingFirstHeight,ite_true,h1,h2,h3]
  simp only [Set.indicator,Set.mem_inter_iff,Set.mem_Ioc,Set.mem_Ioo,Set.mem_Icc]
  by_cases hG : s ∈ G <;> simp only [hG,ite_true,ite_false,Set.mem_univ,Set.notMem_empty]
  all_goals split_ifs <;> simp_all <;> grind

/-- Rectangle discrepancy controls the remaining triangular second case. -/
theorem samplingSecondTriangular_pair_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    [NullSingletonClass (μ.map X)] [NullSingletonClass (μ.map Y)]
    (hXs : ∀ᵐ x ∂μ, X x ∈ Set.Ico (0 : ℝ) 1)
    (hYs : ∀ᵐ x ∂μ, Y x ∈ Set.Ico (0 : ℝ) 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hrect : ∀ a b c d : ℝ,
      |(μ {x | X x ∈ Set.Icc a b ∧ Y x ∈ Set.Icc c d}).toReal -
        (unitIntervalMeasure (Set.Icc a b)).toReal*(unitIntervalMeasure (Set.Icc c d)).toReal| ≤ δ)
    (h α : ℝ) (G : Set ℝ) (a c s : ℝ)
    (hh : 0 < h) (hh1 : h < 1) (hα : 0 < α) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    |(∫ x, samplingOrientedWeight true true h α (Set.Icc a c) G s (X x)*
        samplingOrientedWeight true true h α (Set.Icc a c) G s (Y x) ∂μ)-
      samplingOrientedDensity true true h α (Set.Icc a c) G s^2| ≤ δ := by
  have he := samplingSecondTriangular_reflect h α G a c s
  have hp : (∫ x, samplingOrientedWeight true true h α (Set.Icc a c) G s (X x)*
        samplingOrientedWeight true true h α (Set.Icc a c) G s (Y x) ∂μ) =
      ∫ x, samplingTestedFirstWeight true h α (if s ∈ G then Set.univ else ∅)
        (Set.Icc (1-c) (1-a)) (1-s) (X x)*
        samplingTestedFirstWeight true h α (if s ∈ G then Set.univ else ∅)
        (Set.Icc (1-c) (1-a)) (1-s) (Y x) ∂μ := by
    apply integral_congr_ae
    have hxne : ∀ᵐ x ∂μ, X x ≠ s := ae_of_ae_map hX.aemeasurable
      (ae_iff.mpr (show (μ.map X) {t | ¬t ≠ s} = 0 by simp))
    have hyne : ∀ᵐ x ∂μ, Y x ≠ s := ae_of_ae_map hY.aemeasurable
      (ae_iff.mpr (show (μ.map Y) {t | ¬t ≠ s} = 0 by simp))
    filter_upwards [hXs,hYs,hxne,hyne] with x hx hy hxn hyn
    rw [he (X x) hh hh1 hα hs hx hxn,he (Y x) hh hh1 hα hs hy hyn]
  have hm : samplingOrientedDensity true true h α (Set.Icc a c) G s =
      samplingTestedFirstDensity true h α (if s ∈ G then Set.univ else ∅)
        (Set.Icc (1-c) (1-a)) (1-s) := by
    apply integral_congr_ae
    have : NullSingletonClass unitIntervalMeasure := by unfold unitIntervalMeasure; infer_instance
    filter_upwards [self_mem_ae_restrict measurableSet_Ico,
      ae_iff.mpr (show unitIntervalMeasure {t | ¬t ≠ s} = 0 by simp)] with t ht hts
    exact he t hh hh1 hα hs ht hts
  rw [hp,hm]
  apply (samplingTestedFirst_pair_bound μ X Y hX hY δ hrect true h α _
    (1-c) (1-a) (1-s) hh hh1 hα ⟨by linarith [hs.2],by linarith [hs.1]⟩).trans
  by_cases hG : s ∈ G <;> simp [hG,samplingFirstHeight,hδ]

end
end FiniteFactor

end OAI

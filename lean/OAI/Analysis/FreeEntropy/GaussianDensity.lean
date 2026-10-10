import OAI.Analysis.FreeEntropy.GaussianVolume

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

noncomputable section
open MeasureTheory ProbabilityTheory Set Finset
open scoped ENNReal
namespace FiniteEntropySeparation
 theorem integral_pi_prod {ι : Type u1} [Fintype ι] (f : ι → ℝ → ℝ)
    (s : ι → Set ℝ) (hs : ∀i,MeasurableSet (s i)) :
    ∫ x : ι → ℝ in Set.pi univ s, ∏ i,f i (x i) = ∏ i,∫ x in s i,f i x := by
  classical
  rw [← integral_indicator (MeasurableSet.univ_pi hs)]
  have he : (Set.pi univ s).indicator (fun x : ι → ℝ => ∏ i,f i (x i)) =
      fun x => ∏ i,(s i).indicator (f i) (x i) := by
    funext x
    by_cases h : ∀i,x i ∈ s i
    · simp [Set.indicator_of_mem,Set.mem_pi,h]
    · obtain ⟨i,hi⟩ := not_forall.mp h
      rw [Set.indicator_of_notMem (by simpa only [Set.mem_univ_pi] using not_forall.mpr ⟨i,hi⟩)]
      symm
      exact prod_eq_zero (mem_univ i) (Set.indicator_of_notMem hi _)
  rw [he,integral_fintype_prod_volume_eq_prod]
  simp only [integral_indicator,hs]
 def gaussianDensity {ι : Type u2} [Fintype ι] (x : ι → ℝ) : ℝ :=
    ∏ i,gaussianPDFReal 0 1 (x i)
 theorem gaussianDensity_pos {ι : Type u3} [Fintype ι] (x : ι → ℝ) : 0<gaussianDensity x := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos 0 1 _ one_ne_zero
 theorem gaussianDensity_continuous (ι : Type u4) [Fintype ι] : Continuous (gaussianDensity (ι := ι)) := by
  apply continuous_finsetProd
  intro i _
  unfold gaussianPDFReal
  fun_prop
 theorem gaussianDensity_integrable (ι : Type u5) [Fintype ι] : Integrable (gaussianDensity (ι := ι)) :=
  Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 1)
 theorem productGaussian_withDensity (ι : Type u6) [Fintype ι] :
    productGaussian ι = volume.withDensity (fun x => ENNReal.ofReal (gaussianDensity x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianDensity_integrable ι).integrableOn
    (ae_of_all _ (fun x => (gaussianDensity_pos x).le))]
  change ENNReal.ofReal (∫ x : ι → ℝ in Set.pi univ s, ∏ i,gaussianPDFReal 0 1 (x i)) = _
  rw [integral_pi_prod _ s hs, ENNReal.ofReal_prod_of_nonneg]
  · apply prod_congr rfl
    intro i _
    rw [gaussianReal_apply 0 one_ne_zero,gaussianPDF_def]
    exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
      (ae_of_all _ (gaussianPDFReal_nonneg 0 1))
  · intro i _
    exact integral_nonneg (gaussianPDFReal_nonneg _ _)
 theorem gaussianDensity_formula {ι : Type u7} [Fintype ι] (x : ι → ℝ) :
    gaussianDensity x = (Real.sqrt (2*Real.pi))⁻¹^(Fintype.card ι) * Real.exp (-(∑i,x i^2)/2) := by
  classical
  simp only [gaussianDensity,gaussianPDFReal, NNReal.coe_one,mul_one,sub_zero]
  rw [prod_mul_distrib,prod_const,card_univ,← Real.exp_sum]
  congr 1
  congr 1
  rw [← sum_div,sum_neg_distrib]
end FiniteEntropySeparation

end

end OAI

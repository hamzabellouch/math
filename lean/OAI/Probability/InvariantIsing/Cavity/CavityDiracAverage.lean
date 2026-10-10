import OAI.Probability.InvariantIsing.Cavity.CavityProductDisorderWeighted

namespace OAI

/-! Restoring the original random tree after proving an identity for
each fixed tree, while retaining the rotation and Gaussian disorder. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_bounded_dirac_average {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure A) [IsProbabilityMeasure P] (S : Measure B) [IsProbabilityMeasure S]
    (Q : Measure C) [IsProbabilityMeasure Q] (R : Measure D) [IsProbabilityMeasure R]
    (f : ((A × B) × C) × D → ℝ) (hf : Measurable f) {M : ℝ}
    (hb : ∀ p, |f p| ≤ M) :
    (∫ b, ∫ p, f p ∂((P.prod (Measure.dirac b)).prod Q).prod R ∂S) =
      ∫ p, f p ∂((P.prod S).prod Q).prod R := by
  let g := fun x : A × B => ∫ d, ∫ c, f ((x,c),d) ∂Q ∂ R
  have hm : Measurable (fun p : ((A × B) × D) × C => f ((p.1.1,p.2),p.1.2)) :=
    hf.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  have hg : Measurable g :=
    hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable
  have hgb x : |g x| ≤ M := by
    apply abs_integral_le_const_of_bound
      ((hm.stronglyMeasurable.integral_prod_right'.measurable).comp measurable_prodMk_left)
    intro d
    exact abs_integral_le_const_of_bound (hm.comp measurable_prodMk_left)
      (fun c => hb ((x,c),d))
  have hgi := integrable_of_measurable_abs_le (μ := P.prod S) hg hgb
  simp_rw [cavity_bounded_disorder_dirac_shuffle P _ Q R f hf hb]
  rw [cavity_bounded_disorder_shuffle (P.prod S) Q R f hf hb, integral_prod _ hgi]
  exact (integral_integral_swap hgi).symm

lemma measurable_cavity_bounded_dirac_integral {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure A) [IsProbabilityMeasure P]
    (Q : Measure C) [IsProbabilityMeasure Q] (R : Measure D) [IsProbabilityMeasure R]
    (f : ((A × B) × C) × D → ℝ) (hf : Measurable f) {M : ℝ}
    (hb : ∀ p, |f p| ≤ M) :
    Measurable (fun b => ∫ p, f p ∂((P.prod (Measure.dirac b)).prod Q).prod R) := by
  simp_rw [cavity_bounded_disorder_dirac_shuffle P _ Q R f hf hb]
  have hm : Measurable (fun p : ((A × B) × D) × C => f ((p.1.1,p.2),p.1.2)) :=
    hf.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  have hg : Measurable (fun x : A × B => ∫ d, ∫ c, f ((x,c),d) ∂Q ∂ R) :=
    hm.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable
  exact (hg.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable

end InvariantIsing

end

end OAI

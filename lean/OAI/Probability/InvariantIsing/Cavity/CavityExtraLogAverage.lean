import OAI.Probability.InvariantIsing.Cavity.CavityProductDisorderWeighted

namespace OAI

/-! The two finite-volume Fubini steps needed to retain an independent
compression variable in the logarithmic cavity limit. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_bounded_extra_product_integral {Z A B : Type*}
    [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Z) [IsProbabilityMeasure P] (Q : Measure A) [IsProbabilityMeasure Q]
    (R : Measure B) [IsProbabilityMeasure R]
    (f : (Z × A) × B → ℝ) (hf : Measurable f) {M : ℝ} (hb : ∀ p, |f p| ≤ M) :
    (∫ p, f p ∂(P.prod Q).prod R) =
      ∫ z, ∫ p, f ((z,p.1),p.2) ∂Q.prod R ∂P := by
  have hi : Integrable f ((P.prod Q).prod R) :=
    integrable_of_measurable_abs_le hf hb
  rw [integral_prod _ hi, integral_prod _ hi.integral_prod_left]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  have hm : Measurable (fun p : A × B => f ((z,p.1),p.2)) :=
    hf.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  exact (integral_prod _ (integrable_of_measurable_abs_le hm (fun p => hb ((z,p.1),p.2)))).symm

lemma cavity_bounded_three_integral_cycle {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (R : Measure C) [IsProbabilityMeasure R]
    (f : A × (B × C) → ℝ) (hf : Measurable f) {M : ℝ} (hb : ∀ p, |f p| ≤ M) :
    (∫ a, ∫ p, f (a,p) ∂Q.prod R ∂P) =
      integral Q (fun b => integral P (fun a => integral R (fun c => f (a,(b,c))))) := by
  let g := fun p : (A × B) × C => f (p.1.1,(p.1.2,p.2))
  have hg : Measurable g := hf.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hgb p : |g p| ≤ M := hb _
  have hi : Integrable g ((P.prod Q).prod R) := integrable_of_measurable_abs_le hg hgb
  have he := cavity_bounded_extra_product_integral P Q R g hg hgb
  change (∫ a, ∫ p, g ((a,p.1),p.2) ∂Q.prod R ∂P) = _
  rw [← he, integral_prod _ hi]
  exact integral_prod_symm _ hi.integral_prod_left

end InvariantIsing

end

end OAI

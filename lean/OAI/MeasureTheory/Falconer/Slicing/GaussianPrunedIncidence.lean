import OAI.MeasureTheory.Falconer.Slicing.GaussianPruningSets
import OAI.MeasureTheory.Falconer.Measures.ProductRestrictionLoss

namespace OAI

/-! # Incidence on the original labels after the marginal slice restrictions -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {ι : Type*} [Fintype ι]

noncomputable def gaussianPrunedIncidence
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) (δ : ℝ)
    (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (p : (Fin h → Space d) × Space h) : ℝ≥0∞ :=
  ((gaussianPointSliceMeasure μ p.1 p.2 δ).restrict (gaussianPointGood μ δ r TP p)).prod
    ((gaussianDirectionSliceMeasure ν p.1 δ).restrict (gaussianDirectionGood ν δ r TD M p.1)) E

theorem gaussianPrunedIncidence_measurable
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E) :
    Measurable (gaussianPrunedIncidence (h := h) μ ν δ r TP TD M E) := by
  let G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
    {q | q.2 ∈ E ∧ q.2.1 ∈ gaussianPointGood μ δ r TP q.1 ∧
      q.2.2 ∈ gaussianDirectionGood ν δ r TD M q.1.1}
  have hG : MeasurableSet G := by
    have hp := (gaussianPointGood_measurable_joint (h := h) μ δ r TP).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1,q.2.1)) from by fun_prop)
    have hd := (gaussianDirectionGood_measurable_joint (h := h) ν δ r TD M).preimage
      (show Measurable (fun q : ((Fin h → Space d) × Space h) × (Space d × Sphere d) =>
        (q.1.1,q.2.2)) from by fun_prop)
    exact (hE.preimage measurable_snd).inter (hp.inter hd)
  convert gaussian_pair_restriction_mass_measurable μ ν δ G hG using 1
  ext p
  rw [gaussianPrunedIncidence,Measure.prod_restrict,Measure.restrict_apply hE]
  congr 1

omit [Fintype ι] in
theorem gaussian_pruning_pointwise_loss
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (δ : ℝ) (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (p : (Fin h → Space d) × Space h) :
    (gaussianPointSliceMeasure μ p.1 p.2 δ).prod (gaussianDirectionSliceMeasure ν p.1 δ) E ≤
      gaussianPrunedIncidence μ ν δ r TP TD M E p +
      gaussianPointSliceMeasure μ p.1 p.2 δ (gaussianPointGood μ δ r TP p)ᶜ*M +
      gaussianPointMass μ δ p*gaussianDirectionSliceMeasure ν p.1 δ
        (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD)ᶜ +
      (if M < gaussianDirectionMass ν δ p.1 then
        gaussianPointMass μ δ p*gaussianDirectionMass ν δ p.1 else 0) := by
  have hm : gaussianDirectionSliceMeasure ν p.1 δ univ = gaussianDirectionMass ν δ p.1 := by
    simp [gaussianDirectionSliceMeasure,gaussianDirectionMass,Measure.smul_apply]
  by_cases hM : gaussianDirectionMass ν δ p.1 ≤ M
  · have hd : gaussianDirectionGood ν δ r TD M p.1 =
        finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD := by
      ext w
      simp only [gaussianDirectionGood,mem_ofPred_eq,hM,true_and]
    have hl := product_restriction_incidence_loss (gaussianPointSliceMeasure μ p.1 p.2 δ)
      (gaussianDirectionSliceMeasure ν p.1 δ) E hE (gaussianPointGood μ δ r TP p)
      (finiteBallGood (gaussianDirectionSliceMeasure ν p.1 δ) r TD)
    rw [gaussianPointSliceMeasure_univ,hm] at hl
    simp only [not_lt_of_ge hM,ite_false,add_zero,gaussianPrunedIncidence,hd]
    exact hl.trans (add_le_add (add_le_add le_rfl (mul_le_mul_right hM _)) le_rfl)
  · have hl : (gaussianPointSliceMeasure μ p.1 p.2 δ).prod
        (gaussianDirectionSliceMeasure ν p.1 δ) E ≤
        gaussianPointMass μ δ p*gaussianDirectionMass ν δ p.1 := by
      calc
        _ ≤ (gaussianPointSliceMeasure μ p.1 p.2 δ).prod
            (gaussianDirectionSliceMeasure ν p.1 δ) univ := measure_mono (subset_univ _)
        _ = _ := by rw [← univ_prod_univ,Measure.prod_prod,gaussianPointSliceMeasure_univ,hm]
    simp only [lt_of_not_ge hM,ite_true]
    exact hl.trans (show _ ≤ _ + _ from by
      exact (zero_add _).symm.le.trans (add_le_add bot_le le_rfl))

end Falconer

end OAI

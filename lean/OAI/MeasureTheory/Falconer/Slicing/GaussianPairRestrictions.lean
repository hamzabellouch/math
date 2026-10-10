import OAI.MeasureTheory.Falconer.Slicing.GaussianRestrictedMass

namespace OAI

/-! # Measurable original-pair relations in Gaussian slices -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_pair_restriction_mass_measurable
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [SFinite μ] [SFinite ν]
    (r : ℝ) (G : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)))
    (hG : MeasurableSet G) :
    Measurable (fun p : (Fin h → Space d) × Space h =>
      (gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianDirectionSliceMeasure ν p.1 r)
        {t | (p,t) ∈ G}) := by
  let B : Set (((Fin h → Space d) × Space h) × (Space d × Sphere d)) :=
    {p | p.2.1 ∈ gaussianPointBand p.1.1 p.1.2 r ∧ p.2.2 ∈ gaussianDirectionBand p.1.1 r}
  have hB : MeasurableSet B := by
    change MeasurableSet {p : ((Fin h → Space d) × Space h) × (Space d × Sphere d) |
      (∀ i, |inner ℝ p.2.1 (p.1.1 i)-p.1.2 i| ≤ r) ∧
      ∀ i, |inner ℝ (p.2.2:Space d) (p.1.1 i)| ≤ r}
    simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter
    · exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
    · exact MeasurableSet.iInter (fun _ => measurableSet_le (by fun_prop) measurable_const)
  have hm := parameter_restricted_mass_measurable (μ.prod ν) B G hB hG
  convert (hm.const_mul (ENNReal.ofReal (r^(-(h:ℝ))))).const_mul
    (ENNReal.ofReal (r^(-(h:ℝ)))) using 1
  ext p
  simp only [gaussianPointSliceMeasure,gaussianDirectionSliceMeasure,Measure.prod_smul_left,
    Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul,Measure.prod_restrict]
  rfl

end Falconer

end OAI

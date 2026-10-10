import OAI.MeasureTheory.Falconer.Slicing.GaussianPointMass
import OAI.MeasureTheory.Falconer.Recursion.PotentialPair

namespace OAI

/-! # Localized pairs of Gaussian point slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianPointCloseMass (μ : Measure (Space d))
    (p : (Fin h → Space d) × Space h) (r ρ : ℝ) : ℝ≥0∞ :=
  (μ.prod μ) ({z | dist z.1 z.2 < ρ} ∩
    ((gaussianPointBand p.1 p.2 r) ×ˢ (gaussianPointBand p.1 p.2 r)))

instance gaussianPointSliceMeasure_finite (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (A : Fin h → Space d) (z : Space h) (r : ℝ) : IsFiniteMeasure (gaussianPointSliceMeasure μ A z r) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (r^(-(h:ℝ)))*(μ.restrict (gaussianPointBand A z r)) univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem gaussianPointSlice_close_identity (μ : Measure (Space d)) [SFinite μ]
    (p : (Fin h → Space d) × Space h) (r ρ : ℝ) :
    ((gaussianPointSliceMeasure μ p.1 p.2 r).prod (gaussianPointSliceMeasure μ p.1 p.2 r))
        {z | dist z.1 z.2 < ρ} =
      (ENNReal.ofReal (r^(-(h:ℝ))))^2*gaussianPointCloseMass μ p r ρ := by
  have hD : MeasurableSet {z : Space d × Space d | dist z.1 z.2 < ρ} :=
    measurableSet_lt (by fun_prop) measurable_const
  simp only [gaussianPointSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hD,
    gaussianPointCloseMass,pow_two,mul_assoc]

theorem gaussian_point_close_average (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {r : ℝ} (hr : 0 ≤ r) (ρ : ℝ) :
    (∫⁻ p : (Fin h → Space d) × Space h, gaussianPointCloseMass μ p r ρ
      ∂(gaussianRows d h).prod volume) ≤
      ∫⁻ z in {z : Space d × Space d | dist z.1 z.2 < ρ}, ENNReal.ofReal ((2*r)^h)*
        gaussianRows d h {A | ∀ i, |inner ℝ (z.1-z.2) (A i)| ≤ 2*r} ∂μ.prod μ := by
  let D : Set (Space d × Space d) := {z | dist z.1 z.2 < ρ}
  let S : Set (((Fin h → Space d) × Space h) × (Space d × Space d)) :=
    {p | p.2.1 ∈ gaussianPointBand p.1.1 p.1.2 r ∧ p.2.2 ∈ gaussianPointBand p.1.1 p.1.2 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : ((Fin h → Space d) × Space h) × (Space d × Space d) |
      (∀ i, |inner ℝ p.2.1 (p.1.1 i)-p.1.2 i| ≤ r) ∧
      (∀ i, |inner ℝ p.2.2 (p.1.1 i)-p.1.2 i| ≤ r)}
    simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter <;> apply MeasurableSet.iInter <;> intro i <;>
      exact measurableSet_le (by fun_prop) measurable_const
  have hsection (p : (Fin h → Space d) × Space h) : Prod.mk p ⁻¹' S =
      (gaussianPointBand p.1 p.2 r) ×ˢ (gaussianPointBand p.1 p.2 r) := rfl
  calc
    _ = ∫⁻ p : (Fin h → Space d) × Space h, ((μ.prod μ).restrict D) (Prod.mk p ⁻¹' S)
        ∂(gaussianRows d h).prod volume := by
      apply lintegral_congr
      intro p
      rw [hsection,Measure.restrict_apply
        ((gaussianPointBand_measurable p.1 p.2 r).prod (gaussianPointBand_measurable p.1 p.2 r))]
      simp only [gaussianPointCloseMass,D,inter_comm]
    _ = (((gaussianRows d h).prod volume).prod ((μ.prod μ).restrict D)) S :=
      (Measure.prod_apply hS).symm
    _ = ∫⁻ z in D, ((gaussianRows d h).prod (volume : Measure (Space h)))
        {p | z.1 ∈ gaussianPointBand p.1 p.2 r ∧ z.2 ∈ gaussianPointBand p.1 p.2 r} ∂μ.prod μ :=
      Measure.prod_apply_symm hS
    _ ≤ _ := lintegral_mono (fun z => gaussianPointBand_pair_average z.1 z.2 hr)

end Falconer

end OAI

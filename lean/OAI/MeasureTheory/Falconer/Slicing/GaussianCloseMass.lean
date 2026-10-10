import OAI.MeasureTheory.Falconer.Slicing.GaussianSliceMass
import OAI.MeasureTheory.Falconer.Recursion.PotentialPair

namespace OAI

/-! # Localized pairs in the actual Gaussian direction slices -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianDirectionSliceMeasure (ν : Measure (Sphere d))
    (A : Fin h → Space d) (r : ℝ) : Measure (Sphere d) :=
  ENNReal.ofReal (r^(-(h:ℝ))) • ν.restrict (gaussianDirectionBand A r)

instance gaussianDirectionSliceMeasure_finite (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    (A : Fin h → Space d) (r : ℝ) : IsFiniteMeasure (gaussianDirectionSliceMeasure ν A r) := by
  refine ⟨?_⟩
  change ENNReal.ofReal (r^(-(h:ℝ)))*(ν.restrict (gaussianDirectionBand A r)) univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

noncomputable def gaussianDirectionCloseMass (ν : Measure (Sphere d))
    (A : Fin h → Space d) (r ρ : ℝ) : ℝ≥0∞ :=
  (ν.prod ν) ({z | dist z.1 z.2 < ρ} ∩
    ((gaussianDirectionBand A r) ×ˢ (gaussianDirectionBand A r)))

theorem gaussianDirectionSlice_close_identity (ν : Measure (Sphere d)) [SFinite ν]
    (A : Fin h → Space d) (r ρ : ℝ) :
    ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))
        {z | dist z.1 z.2 < ρ} =
      (ENNReal.ofReal (r^(-(h:ℝ))))^2*gaussianDirectionCloseMass ν A r ρ := by
  have hD : MeasurableSet {z : Sphere d × Sphere d | dist z.1 z.2 < ρ} :=
    measurableSet_lt (by fun_prop) measurable_const
  simp only [gaussianDirectionSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hD,
    gaussianDirectionCloseMass,pow_two,mul_assoc]

theorem gaussian_direction_close_average (ν : Measure (Sphere d)) [SFinite ν] (r ρ : ℝ) :
    (∫⁻ A : Fin h → Space d, gaussianDirectionCloseMass ν A r ρ ∂gaussianRows d h) =
      ∫⁻ z in {z : Sphere d × Sphere d | dist z.1 z.2 < ρ},
        gaussianRows d h {A | ∀ i,
          |inner ℝ (z.1:Space d) (A i)| ≤ r ∧ |inner ℝ (z.2:Space d) (A i)| ≤ r} ∂ν.prod ν := by
  let D : Set (Sphere d × Sphere d) := {z | dist z.1 z.2 < ρ}
  let S : Set ((Fin h → Space d) × (Sphere d × Sphere d)) := {p | ∀ i,
    |inner ℝ (p.2.1:Space d) (p.1 i)| ≤ r ∧ |inner ℝ (p.2.2:Space d) (p.1 i)| ≤ r}
  have hD : MeasurableSet D := measurableSet_lt (by fun_prop) measurable_const
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall,ofPred_and]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const)
  have hsection (A : Fin h → Space d) : Prod.mk A ⁻¹' S =
      (gaussianDirectionBand A r) ×ˢ (gaussianDirectionBand A r) := by
    ext z
    simp only [S,gaussianDirectionBand,mem_preimage,mem_ofPred_eq,mem_prod]
    exact forall_and
  calc
    _ = ∫⁻ A : Fin h → Space d, ((ν.prod ν).restrict D) (Prod.mk A ⁻¹' S) ∂gaussianRows d h := by
      apply lintegral_congr
      intro A
      rw [hsection,Measure.restrict_apply
        ((gaussianDirectionBand_measurable A r).prod (gaussianDirectionBand_measurable A r))]
      simp only [gaussianDirectionCloseMass,D,inter_comm]
    _ = ((gaussianRows d h).prod ((ν.prod ν).restrict D)) S := (Measure.prod_apply hS).symm
    _ = _ := Measure.prod_apply_symm hS

end Falconer

end OAI

import OAI.MeasureTheory.Falconer.Slicing.GaussianCloseMass
import OAI.MeasureTheory.Falconer.Slicing.GaussianTripleBand

namespace OAI

/-! # Averaging the actual three-label direction slice law -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

def directionTripleBand (A : Fin h → Space d) (r : ℝ) :
    Set (Sphere d × Sphere d × Sphere d) :=
  gaussianDirectionBand A r ×ˢ (gaussianDirectionBand A r ×ˢ gaussianDirectionBand A r)

theorem directionTripleBand_measurable (A : Fin h → Space d) (r : ℝ) :
    MeasurableSet (directionTripleBand A r) :=
  (gaussianDirectionBand_measurable A r).prod
    ((gaussianDirectionBand_measurable A r).prod (gaussianDirectionBand_measurable A r))

theorem gaussian_direction_triple_identity (ν : Measure (Sphere d)) [SFinite ν]
    (A : Fin h → Space d) (r : ℝ) (E : Set (Sphere d × Sphere d × Sphere d))
    (hE : MeasurableSet E) :
    ((gaussianDirectionSliceMeasure ν A r).prod
      ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))) E =
      (ENNReal.ofReal (r^(-(h:ℝ))))^3*(ν.prod (ν.prod ν)) (E ∩ directionTripleBand A r) := by
  simp only [gaussianDirectionSliceMeasure,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,Measure.restrict_apply hE,
    directionTripleBand,pow_succ,pow_zero,one_mul,mul_assoc]

theorem gaussian_direction_triple_average (ν : Measure (Sphere d)) [SFinite ν]
    (r : ℝ) (E : Set (Sphere d × Sphere d × Sphere d)) (hE : MeasurableSet E) :
    (∫⁻ A : Fin h → Space d, ((gaussianDirectionSliceMeasure ν A r).prod
      ((gaussianDirectionSliceMeasure ν A r).prod (gaussianDirectionSliceMeasure ν A r))) E
        ∂gaussianRows d h) =
    (ENNReal.ofReal (r^(-(h:ℝ))))^3 *
      ∫⁻ w in E, gaussianRows d h {A | ∀ i,
        |inner ℝ (w.1:Space d) (A i)| ≤ r ∧
        |inner ℝ (w.2.1:Space d) (A i)| ≤ r ∧
        |inner ℝ (w.2.2:Space d) (A i)| ≤ r} ∂ν.prod (ν.prod ν) := by
  simp_rw [gaussian_direction_triple_identity ν _ r E hE]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_succ,pow_two]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top)]
  congr 1
  let S : Set ((Fin h → Space d) × (Sphere d × Sphere d × Sphere d)) :=
    {p | ∀ i, |inner ℝ (p.2.1:Space d) (p.1 i)| ≤ r ∧
      |inner ℝ (p.2.2.1:Space d) (p.1 i)| ≤ r ∧
      |inner ℝ (p.2.2.2:Space d) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall,ofPred_and]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      ((measurableSet_le (by fun_prop) measurable_const).inter
        (measurableSet_le (by fun_prop) measurable_const))
  have hs (A : Fin h → Space d) : Prod.mk A ⁻¹' S = directionTripleBand A r := by
    ext w
    simp only [S,directionTripleBand,gaussianDirectionBand,mem_preimage,mem_ofPred_eq,mem_prod,forall_and]
  calc
    _ = ∫⁻ A : Fin h → Space d, ((ν.prod (ν.prod ν)).restrict E) (Prod.mk A ⁻¹' S)
        ∂gaussianRows d h := by
      apply lintegral_congr
      intro A
      rw [hs,Measure.restrict_apply (directionTripleBand_measurable A r)]
      rw [inter_comm]
    _ = ((gaussianRows d h).prod ((ν.prod (ν.prod ν)).restrict E)) S := (Measure.prod_apply hS).symm
    _ = _ := Measure.prod_apply_symm hS

end Falconer

end OAI

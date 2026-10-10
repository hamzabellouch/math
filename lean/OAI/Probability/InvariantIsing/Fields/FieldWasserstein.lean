import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldExtension
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! First-moment transport is the infimum of the costs of joint laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace InvariantIsing

structure FieldLawCoupling (μ ν : ProbabilityMeasure ℝ) where
  law : ProbabilityMeasure (ℝ × ℝ)
  fst : (law : Measure (ℝ × ℝ)).map Prod.fst=(μ : Measure ℝ)
  snd : (law : Measure (ℝ × ℝ)).map Prod.snd=(ν : Measure ℝ)

namespace FieldLawCoupling

variable {μ ν : ProbabilityMeasure ℝ}

def cost (p : FieldLawCoupling μ ν) : ℝ≥0∞ :=
  ∫⁻ xy, ENNReal.ofReal |xy.1-xy.2| ∂(p.law : Measure (ℝ × ℝ))

lemma integrable_fst (p : FieldLawCoupling μ ν)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ)) :
    Integrable (fun xy : ℝ × ℝ => xy.1) (p.law : Measure (ℝ × ℝ)) := by
  rw [← p.fst] at hμ
  exact (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).mp hμ

lemma integrable_snd (p : FieldLawCoupling μ ν)
    (hν : Integrable (fun x : ℝ => x) (ν : Measure ℝ)) :
    Integrable (fun xy : ℝ × ℝ => xy.2) (p.law : Measure (ℝ × ℝ)) := by
  rw [← p.snd] at hν
  exact (integrable_map_measure (by fun_prop) measurable_snd.aemeasurable).mp hν

lemma cost_eq_ofReal (p : FieldLawCoupling μ ν)
    (hμ : Integrable (fun x : ℝ => x) (μ : Measure ℝ))
    (hν : Integrable (fun x : ℝ => x) (ν : Measure ℝ)) :
    p.cost=ENNReal.ofReal (∫ xy, |xy.1-xy.2| ∂(p.law : Measure (ℝ × ℝ))) := by
  symm
  exact ofReal_integral_eq_lintegral_ofReal
    ((p.integrable_fst hμ).sub (p.integrable_snd hν)).abs (ae_of_all _ (fun _ => abs_nonneg _))

end FieldLawCoupling

def fieldWassersteinOne (μ ν : ProbabilityMeasure ℝ) : ℝ≥0∞ :=
  ⨅ p : FieldLawCoupling μ ν, p.cost

lemma exists_fieldLawCoupling_cost_lt {μ ν : ProbabilityMeasure ℝ} {ε : ℝ≥0∞}
    (h : fieldWassersteinOne μ ν < ε) :
    ∃ p : FieldLawCoupling μ ν, p.cost < ε :=
  (iInf_lt_iff).mp h

end InvariantIsing

end

end OAI

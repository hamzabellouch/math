import OAI.Analysis.FiniteFactor.Coupling.Bounds
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- A probability density gives an actual probability measure. -/
theorem densityMeasure_probability {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {d : X → ℝ} (hd : Integrable d μ)
    (h0 : ∀ x, 0 ≤ d x) (hm : ∫ x, d x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (d x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hd (Filter.Eventually.of_forall h0), hm]
  simp

namespace CouplingParameters
variable (p : CouplingParameters)

def endpointComponentLaw (right : Bool) (i : Fin 5) : Measure ℝ :=
  unitIntervalMeasure.withDensity (fun t => ENNReal.ofReal (p.endpointComponentDensity right i t))

instance endpointComponentLaw_probability (right : Bool) (i : Fin 5) :
    IsProbabilityMeasure (p.endpointComponentLaw right i) := by
  apply densityMeasure_probability
  · exact intervalDensity_integrable (p.endpointInterval_measurable right i) _
  · exact intervalDensity_nonneg (p.endpointLength_pos right i).le
  · exact intervalDensity_integral (p.endpointInterval_measurable right i)
      (p.endpointLength_pos right i) (p.endpointInterval_mass right i)

/-- Six labels: zero is diagonal; the five successors retain both widths and the tag. -/
def labelMass : Fin 6 → ℝ := Fin.cons p.diagonalMass p.replacementMass

def pairComponentLaw : Fin 6 → Measure (ℝ × ℝ) :=
  Fin.cons (unitIntervalMeasure.map (fun t => (t,t)))
    (fun i => (p.endpointComponentLaw false i).prod (p.endpointComponentLaw true i))

theorem labelMass_nonneg (i : Fin 6) : 0 ≤ p.labelMass i := by
  refine Fin.cases p.diagonalMass_pos.le (fun i => p.replacementMass_nonneg i) i

theorem labelMass_sum : ∑ i, p.labelMass i = 1 := by
  simpa [labelMass, Fin.sum_univ_succ] using p.mass_sum

instance pairComponentLaw_probability (i : Fin 6) : IsProbabilityMeasure (p.pairComponentLaw i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · constructor
    have hm : Measurable (fun t : ℝ => (t,t)) := measurable_id.prodMk measurable_id
    rw [pairComponentLaw, Fin.cons_zero, Measure.map_apply hm MeasurableSet.univ]
    simp
  · change IsProbabilityMeasure ((p.endpointComponentLaw false i).prod (p.endpointComponentLaw true i))
    infer_instance

/-- The actual augmented one-coordinate law, including its mixture label. -/
def labelledCoupling : Measure (Fin 6 × (ℝ × ℝ)) :=
  ∑ i, ENNReal.ofReal (p.labelMass i) •
    (p.pairComponentLaw i).map (fun xy => (i,xy))

instance labelledCoupling_probability : IsProbabilityMeasure p.labelledCoupling := by
  constructor
  have hmap (i : Fin 6) : ((p.pairComponentLaw i).map (fun xy => (i,xy))) Set.univ = 1 := by
    have hm : Measurable (fun xy : ℝ × ℝ => (i,xy)) := measurable_const.prodMk measurable_id
    rw [Measure.map_apply hm MeasurableSet.univ]
    simp
  simp only [labelledCoupling, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    hmap, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.labelMass_nonneg i), p.labelMass_sum]
  simp

/-- Forgetting labels gives the one-coordinate pair law. -/
def coupling : Measure (ℝ × ℝ) := p.labelledCoupling.map Prod.snd

instance coupling_probability : IsProbabilityMeasure p.coupling := by
  constructor
  rw [coupling, Measure.map_apply measurable_snd MeasurableSet.univ]
  simp

theorem endpointComponentLaw_eq (right : Bool) (i : Fin 5) :
    p.endpointComponentLaw right i = ENNReal.ofReal ((p.endpointLength right i)⁻¹) •
      unitIntervalMeasure.restrict (p.endpointInterval right i) := by
  unfold endpointComponentLaw endpointComponentDensity intervalDensity
  have heq : (fun t => ENNReal.ofReal ((p.endpointInterval right i).indicator
      (fun _ => (p.endpointLength right i)⁻¹) t)) =
      (p.endpointInterval right i).indicator (fun _ => ENNReal.ofReal ((p.endpointLength right i)⁻¹)) := by
    funext t
    by_cases ht : t ∈ p.endpointInterval right i <;> simp [ht]
  rw [heq, withDensity_indicator (p.endpointInterval_measurable right i), withDensity_const]

theorem endpointComponentLaw_of_contains (right : Bool) (i : Fin 5) {S : Set ℝ}
    (hS : p.endpointInterval right i ⊆ S) : p.endpointComponentLaw right i S = 1 := by
  have hu := measure_univ (μ := p.endpointComponentLaw right i)
  rw [p.endpointComponentLaw_eq, Measure.smul_apply,
    Measure.restrict_apply' (p.endpointInterval_measurable right i), Set.univ_inter] at hu
  rw [p.endpointComponentLaw_eq, Measure.smul_apply,
    Measure.restrict_apply' (p.endpointInterval_measurable right i), Set.inter_eq_right.mpr hS]
  exact hu

end CouplingParameters
end
end FiniteFactor

end OAI

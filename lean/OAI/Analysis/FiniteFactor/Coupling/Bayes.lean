import OAI.Analysis.FiniteFactor.Coupling.Crossing
import OAI.Analysis.FiniteFactor.Coupling.Marginals
import Mathlib.Probability.Kernel.Basic

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters
variable (p : CouplingParameters)

theorem endpointDensity_measurable (right : Bool) : Measurable (p.endpointDensity right) := by
  apply Measurable.add measurable_const
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul (p.endpointComponentDensity_measurable right i)

theorem posteriorMass_measurable (right : Bool) (i : Fin 5) :
    Measurable (fun t => p.posteriorMass right t i) :=
  (measurable_const.mul (p.endpointComponentDensity_measurable right i)).div
    (p.endpointDensity_measurable right)

def posteriorKernel (right : Bool) : Kernel ℝ ℝ where
  toFun := p.posteriorLaw right
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [posteriorLaw, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Measurable.add
    · exact (measurable_const.div (p.endpointDensity_measurable right)).ennreal_ofReal.mul
        ((Measure.measurable_coe hS).comp Measure.measurable_dirac)
    · exact Finset.measurable_sum _ fun i _ =>
        (p.posteriorMass_measurable right i).ennreal_ofReal.mul measurable_const

instance posteriorKernel_markov (right : Bool) : IsMarkovKernel (p.posteriorKernel right) :=
  ⟨fun t => p.posteriorLaw_probability right t⟩

theorem posteriorLaw_weighted (right : Bool) (t : ℝ) (S : Set ℝ) :
    ENNReal.ofReal (p.endpointDensity right t) * p.posteriorLaw right t S =
      ENNReal.ofReal p.diagonalMass * Measure.dirac t S +
        ∑ i, ENNReal.ofReal (p.replacementMass i) *
          ENNReal.ofReal (p.endpointComponentDensity right i t) * p.endpointComponentLaw (!right) i S := by
  have hh := p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)
  have hc (a : ℝ) : p.endpointDensity right t * (a / p.endpointDensity right t) = a := by
    field_simp [hh.ne']
  simp only [posteriorLaw, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    mul_add, Finset.mul_sum]
  congr 1
  · rw [← mul_assoc, ← ENNReal.ofReal_mul hh.le, hc]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, ← ENNReal.ofReal_mul hh.le, posteriorMass, hc,
      ENNReal.ofReal_mul (p.replacementMass_nonneg i)]

theorem coupling_rectangle {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    p.coupling (A ×ˢ B) = ENNReal.ofReal p.diagonalMass * unitIntervalMeasure (A ∩ B) +
      ∑ i, ENNReal.ofReal (p.replacementMass i) *
        p.endpointComponentLaw false i A * p.endpointComponentLaw true i B := by
  have hm : Measurable (fun t : ℝ => (t,t)) := measurable_id.prodMk measurable_id
  have hdiag : (unitIntervalMeasure.map (fun t => (t,t))) (A ×ˢ B) =
      unitIntervalMeasure (A ∩ B) := by
    rw [Measure.map_apply hm (hA.prod hB)]
    rfl
  simp [p.coupling_eq_sum, Fin.sum_univ_succ, labelMass,
    pairComponentLaw, smul_eq_mul, hdiag, Measure.prod_prod, mul_assoc]

/-- The posterior formula satisfies the defining conditional-law identity on
all measurable rectangles, in either endpoint orientation. -/
theorem posterior_rectangle_integral (right : Bool) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ t in A, p.posteriorLaw right t B ∂(p.coupling.map (endpoint right))) =
      ENNReal.ofReal p.diagonalMass * unitIntervalMeasure (A ∩ B) +
        ∑ i, ENNReal.ofReal (p.replacementMass i) *
          p.endpointComponentLaw right i A * p.endpointComponentLaw (!right) i B := by
  have hk : Measurable (fun t => p.posteriorLaw right t B) :=
    (Measure.measurable_coe hB).comp (p.posteriorKernel right).measurable
  rw [p.coupling_endpoint_density,
    setLIntegral_withDensity_eq_setLIntegral_mul unitIntervalMeasure
      (p.endpointDensity_measurable right).ennreal_ofReal hk hA]
  change (∫⁻ t in A, ENNReal.ofReal (p.endpointDensity right t) * p.posteriorLaw right t B
    ∂unitIntervalMeasure) = _
  simp_rw [p.posteriorLaw_weighted]
  have hd : Measurable (fun t : ℝ => Measure.dirac t B) :=
    (Measure.measurable_coe hB).comp Measure.measurable_dirac
  rw [lintegral_add_left
    (f := fun t => ENNReal.ofReal p.diagonalMass * Measure.dirac t B)
    (g := fun t => ∑ i, ENNReal.ofReal (p.replacementMass i) *
      ENNReal.ofReal (p.endpointComponentDensity right i t) * p.endpointComponentLaw (!right) i B)
    (measurable_const.mul hd),
    lintegral_finsetSum (f := fun i t => ENNReal.ofReal (p.replacementMass i) *
      ENNReal.ofReal (p.endpointComponentDensity right i t) * p.endpointComponentLaw (!right) i B)
      Finset.univ (fun i _ =>
      (measurable_const.mul (p.endpointComponentDensity_measurable right i).ennreal_ofReal).mul measurable_const)]
  congr 1
  · rw [lintegral_const_mul _ hd]
    simp only [Measure.dirac_apply' _ hB]
    rw [lintegral_indicator hB]
    simp [Measure.restrict_apply hB, Set.inter_comm]
  · apply Finset.sum_congr rfl
    intro i _
    have hi := (p.endpointComponentDensity_measurable right i).ennreal_ofReal
    rw [lintegral_mul_const (p.endpointComponentLaw (!right) i B)
      (f := fun t => ENNReal.ofReal (p.replacementMass i) * ENNReal.ofReal (p.endpointComponentDensity right i t))
      (measurable_const.mul hi), lintegral_const_mul _ hi]
    simp only [endpointComponentLaw]
    rw [withDensity_apply _ hA]

/-- Genuine forward disintegration of the constructed coupling. -/
theorem conditional_given_x {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ t in A, p.posteriorKernel false t B ∂(p.coupling.map Prod.fst)) = p.coupling (A ×ˢ B) := by
  rw [p.coupling_rectangle hA hB]
  exact p.posterior_rectangle_integral false hA hB

/-- Genuine reverse disintegration of the same coupling. -/
theorem conditional_given_y {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ t in A, p.posteriorKernel true t B ∂(p.coupling.map Prod.snd)) = p.coupling (B ×ˢ A) := by
  rw [p.coupling_rectangle hB hA]
  have hi := p.posterior_rectangle_integral true hA hB
  simp only [Bool.not_true] at hi
  change (∫⁻ t in A, p.posteriorLaw true t B ∂(p.coupling.map (endpoint true))) = _
  rw [hi, Set.inter_comm A B]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end CouplingParameters
end
end FiniteFactor

end OAI

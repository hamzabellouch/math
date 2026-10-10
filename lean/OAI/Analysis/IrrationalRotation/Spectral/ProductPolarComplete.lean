import OAI.Analysis.IrrationalRotation.Spectral.ProductPolarAssembly
import OAI.Analysis.IrrationalRotation.Spectral.ProductPolarDiffuse
import OAI.Analysis.IrrationalRotation.Product.ProductWeightNonconstant

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel

theorem productPolarStructure_of_weight_not_ae_constant
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c)
    (hnonconstant : ¬ ∃ a : ℝ, weight θ c =ᵐ[baseMeasure] Function.const Base a) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  apply productPolarStructure_of_weightOrbitDiffuse θ c
    (fun i => ⟨(hadm.1 i).1.le, (hadm.1 i).2.1⟩)
    (fun i => (hadm.1 i).2.2.le) hadm.2.1
  rw [star_shift_weightedOperator_eq_multiplier]
  obtain ⟨S, hS, -, hmem⟩ := ae_weight_mem_countable θ c
    (fun i => ⟨(hadm.1 i).1.le, (hadm.1 i).2.1⟩)
    (fun i => (hadm.1 i).2.2.le) hadm.2.1
  exact fullPolarAlgebra_multiplier_diffuse_of_null_fibers θ (weight θ c) 1
    (by norm_num) (measurable_weight θ c) (weight_complex_norm_le_one θ c)
    ⟨S, hS, hmem⟩
    (rotation_joint_fiber_measure_zero hadm.2.2 (measurable_weight θ c) hnonconstant)

theorem productPolarStructure_of_admissible
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) :=
  productPolarStructure_of_weight_not_ae_constant θ c hadm
    (weight_not_ae_constant θ c hadm)

theorem productPolarStructure_of_negInfiniteLogIntegral
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c)
    (hlog : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  apply productPolarStructure_of_weight_not_ae_constant θ c hadm
  exact not_ae_constant_of_negInfiniteLogIntegral
    ((ae_weight_pos θ c (fun i => (hadm.1 i).1.le)
      (fun i => (hadm.1 i).2.2.le) hadm.2.1).mono fun _ h => h.ne') hlog

theorem productPolarStructure_of_divergent_cost
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  exact productPolarStructure_of_weightOrbitDiffuse θ c
    (fun i => ⟨(hadm.1 i).1.le, (hadm.1 i).2.1⟩)
    (fun i => (hadm.1 i).2.2.le) hadm.2.1
    (fullPolarAlgebra_weight_diffuse θ c hadm hdiv)

end Invariant233.ProductModel

end

end OAI

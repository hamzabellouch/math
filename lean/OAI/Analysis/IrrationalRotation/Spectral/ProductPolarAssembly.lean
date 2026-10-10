import OAI.Analysis.IrrationalRotation.Spectral.ProductWeightPolar
import OAI.Analysis.IrrationalRotation.Spectral.ProductPolarModulusComplex

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductModel

theorem operatorModulus_eq_star_shift_weightedOperator (θ c : ℕ → ℝ) :
    operatorModulus (weightedOperator θ c) = star shiftOperator * weightedOperator θ c := by
  rw [star_shift_weightedOperator_eq_multiplier]
  exact GlobalPolarSupport.operatorModulus_weightedOperator θ c
    (measurable_weight θ c).complex_ofReal (weight_complex_norm_le_one θ c)

theorem productPolarStructure_of_fullPolarDiffuse
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hdiff : IsDiffuseVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator (operatorModulus (weightedOperator θ c)))) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  have hu := Unitary.mem_iff.mp GlobalPolarSupport.shiftOperator_mem_unitary
  have hmod := operatorModulus_eq_star_shift_weightedOperator θ c
  refine ⟨hu.1, hu.2, GlobalPolarSupport.weightedOperator_eq_shift_mul_modulus θ c,
    ?_, ?_, ?_, ?_, hdiff⟩
  · rw [hmod]
    exact weight_multiplier_injective θ c (fun i => (hθ01 i).1) hc hθ
  · rw [hmod]
    exact weight_hasCountablyAtomicSpectralType θ c hθ01 hc hθ
  · intro F
    rw [hmod]
    exact finitePolarAlgebra_weight_atomic θ c hθ01 hc hθ F
  · rw [hmod]
    exact fullPolarAlgebra_weight_abelian θ c

theorem productPolarStructure_of_weightOrbitDiffuse
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hdiff : IsDiffuseVonNeumannAlgebra
      (fullPolarAlgebra shiftOperator (star shiftOperator * weightedOperator θ c))) :
    ProductPolarStructure shiftOperator (weightedOperator θ c) := by
  apply productPolarStructure_of_fullPolarDiffuse θ c hθ01 hc hθ
  rwa [operatorModulus_eq_star_shift_weightedOperator]

end Invariant233.ProductModel

end

end OAI

import OAI.Analysis.IrrationalRotation.Spectral.ProductPolarComplete
import OAI.Analysis.IrrationalRotation.Product.ProductHilbert

namespace OAI

noncomputable section

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem finitePolarAlgebra_le_fullPolarAlgebra
    (U B : H →L[ℂ] H) (F : Finset ℤ) :
    finitePolarAlgebra U B F ≤ fullPolarAlgebra U B := by
  apply vonNeumannGenerated_le
  rintro A ⟨n, _hn, rfl⟩
  exact subset_vonNeumannGenerated _ ⟨n, rfl⟩

theorem not_isDiffuse_of_isAtomic [Nontrivial H] (M : VonNeumannAlgebra H)
    (hat : IsAtomicVonNeumannAlgebra M) : ¬ IsDiffuseVonNeumannAlgebra M := by
  intro hdiff
  obtain ⟨p, hp, _⟩ := hat 1 (one_mem M) (IsStarProjection.one _) one_ne_zero
  exact hdiff p hp

theorem ProductPolarStructure.finitePolarAlgebra_lt_fullPolarAlgebra
    [Nontrivial H] {U T : H →L[ℂ] H}
    (h : ProductPolarStructure U T) (F : Finset ℤ) :
    finitePolarAlgebra U (operatorModulus T) F <
      fullPolarAlgebra U (operatorModulus T) := by
  apply lt_of_le_of_ne (finitePolarAlgebra_le_fullPolarAlgebra _ _ _)
  intro heq
  have hat := (h.2.2.2.2.2.1 F).2
  rw [heq] at hat
  exact not_isDiffuse_of_isAtomic _ hat h.2.2.2.2.2.2.2

namespace ProductModel

theorem finitePolarAlgebra_lt_fullPolarAlgebra_of_logIntegral
    (θ c : ℕ → ℝ) (hadm : AdmissibleAnglesAndCosts θ c)
    (hlog : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) (F : Finset ℤ) :
    finitePolarAlgebra shiftOperator (operatorModulus (weightedOperator θ c)) F <
      fullPolarAlgebra shiftOperator (operatorModulus (weightedOperator θ c)) :=
  ProductPolarStructure.finitePolarAlgebra_lt_fullPolarAlgebra
    (productPolarStructure_of_negInfiniteLogIntegral θ c hadm hlog) F

end ProductModel
end Invariant233

end

end OAI

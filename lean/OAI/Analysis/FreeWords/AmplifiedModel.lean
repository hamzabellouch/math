import Mathlib
import OAI.Analysis.FreeWords.AmplifiedModelDefinitions
import OAI.Analysis.FreeWords.BlockMatrixEmbedding
import OAI.Analysis.FreeWords.NumericalModel

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer KKVariableUltra KKMatrixExpectation KKBlockMatrix KKFactorSupport KKProjectionSupport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance amplifiedModelOrder (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance amplifiedModelPreorder (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance amplifiedModelLE (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance amplifiedModelSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem finite_amplified_numerical_model : FiniteAmplifiedNumericalModel (H := H) := by
  classical
  intro M τ hF hD n hn K F hne hc ε hε
  obtain ⟨d,hd,V,hVK,hVF⟩ := finite_numerical_model M τ hF hD n hn K F hne hc ε hε
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨ρ,hρ,hτρ⟩ := exists_matrix_subfactor M τ hF hD d hd
  let φ := blockHom (ι := Fin n) ρ
  let U : unitary (MatrixAlgebra n M) := ⟨φ V.val,Unitary.map_mem φ V.property⟩
  have hp (k : ℤ) : φ (V^k).val=(U^k).val := unitary_preimage_zpow φ V U rfl k
  have hτ (X) : matrixTrace τ n (φ X)=((n*d:ℕ):ℂ)⁻¹*Matrix.trace X :=
    blockHom_trace ρ τ.map τ.normalized τ.tracial X
  refine ⟨d,hd,ρ,hρ,U,?_,?_,?_⟩
  · intro i j
    exact blockHom_entry_mem ρ V.val i j
  · intro k hk hk0
    rw [← hp k,hτ]
    exact hVK k hk hk0
  · intro w hw
    have he : φ ((w.map (fun z => (V^z.1).val*Matrix.kronecker z.2 1)).prod)=
        ((w.map (fun z => (U^z.1).val*numericalHom (A := ConcreteAlgebra M) n z.2)).prod) := by
      rw [map_list_prod,List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro z hz
      exact (map_mul φ _ _).trans (congrArg₂ (·*·) (hp z.1) (blockHom_kronecker ρ z.2))
    rw [← he,hτ]
    exact hVF w hw

end

end KKFreeLiftFrontier
end

end OAI

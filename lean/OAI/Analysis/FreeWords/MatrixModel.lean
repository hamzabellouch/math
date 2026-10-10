import Mathlib
import OAI.Analysis.FreeWords.CoordinateConstantFree
import OAI.Analysis.FreeWords.MatrixExtendSize
import OAI.Analysis.FreeWords.MatrixModelDefinitions
import OAI.Analysis.FreeWords.VariableMatrixUltra

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKFreeLiftFrontier KKUltraTrace KKFactorSupport

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixModelConcreteOrder (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance matrixModelConcretePreorder (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance matrixModelConcreteLE (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance matrixModelConcreteSOR (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem finite_matrix_model : FiniteMatrixModel (H := H) := by
  classical
  intro M τ hF hD n hn β K F hFne hcenter ε hε
  choose ρ hρ hβ hτρ using (fun j : ℕ => matrix_extension_size M τ hF hD n (2^j)
    hn (by positivity) β)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le atTop
  have hf := matrix_ultra_factor n ρ (tracePositive τ) τ.normalized τ.tracial
    (gnsVector_injective τ) hρ ω hω
  have hd := matrix_ultra_diffuse n ρ hn (tracePositive τ) τ.normalized τ.tracial
    (gnsVector_injective τ) hρ hτρ ω hω
  obtain ⟨j,_,u,huR,huK,huF⟩ := coordinate_constant_free (fun j => (ρ j).range)
    (tracePositive τ) τ.normalized τ.tracial ω hω hf hd K F hFne
    (fun w hw z hz => ⟨(hcenter w hw z hz).1,(hcenter w hw z hz).2.1⟩)
    (fun w hw z hz j => hβ j (hcenter w hw z hz).2.2) ε hε 0
  exact ⟨j,ρ j,hρ j,hβ j,u,huR,huK,huF⟩

end

end KKVariableUltra
end

end OAI

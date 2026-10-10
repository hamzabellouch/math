import Mathlib
import OAI.Analysis.FreeWords.FactorDiffuseCriterion
import OAI.Analysis.FreeWords.MatrixDyadicArithmetic
import OAI.Analysis.FreeWords.MatrixRangeProjections
import OAI.Analysis.FreeWords.MatrixRangeWitness
import OAI.Analysis.FreeWords.VariableUltraFactor
import OAI.Analysis.FreeWords.VariableUltraProjection

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKUltraTrace KKFreeLiftFrontier

open Filter Topology

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (d : ℕ) (ρ : ∀ j : ℕ, Matrix (Fin (d*2^j)) (Fin (d*2^j)) ℂ →⋆ₐ[ℂ] A)

local instance matrixUltraOrder : PartialOrder (coordinateAlgebra (fun j => (ρ j).range)) := CStarAlgebra.spectralOrder _

local instance : LE (coordinateAlgebra (fun j => (ρ j).range)) := (matrixUltraOrder d ρ).toLE

local instance : Preorder (coordinateAlgebra (fun j => (ρ j).range)) := (matrixUltraOrder d ρ).toPreorder

local instance : StarOrderedRing (coordinateAlgebra (fun j => (ρ j).range)) := CStarAlgebra.spectralOrderedRing _

def matrixUltraNormalTrace (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (ω : Ultrafilter ℕ) :
    FaithfulNormalTrace (gnsVonNeumann (coordinateTrace (fun j => (ρ j).range) τ ω)) :=
  gnsNormalTrace (coordinateTrace (fun j => (ρ j).range) τ ω)
    (coordinateTrace_one (fun j => (ρ j).range) τ ω h1)
    (coordinateTrace_tracial (fun j => (ρ j).range) τ ω htr)

theorem matrix_ultra_factor (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (hinj : Function.Injective (gnsVector τ))
    (hρ : ∀ j, Function.Injective (ρ j)) (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤atTop) :
    IsFactor (gnsVonNeumann (coordinateTrace (fun j => (ρ j).range) τ ω)) := by
  apply coordinate_factor _ τ htr _ ω hω
  intro j x hx
  exact matrix_range_commutator_witness (ρ j) (hρ j) τ htr h1 hinj x hx

theorem matrix_ultra_projection (hd : 0<d) (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ x y, τ (x*y)=τ (y*x))
    (hτ : ∀ j x, τ (ρ j x)=((d*2^j:ℕ):ℂ)⁻¹*Matrix.trace x)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤atTop) (m : ℕ) :
    ∃ p : ConcreteAlgebra (gnsVonNeumann (coordinateTrace (fun j => (ρ j).range) τ ω)),
      IsStarProjection p ∧
      (matrixUltraNormalTrace d ρ τ h1 htr ω).map p=(((2:ℝ)^m)⁻¹:ℝ) := by
  have hr (j : ℕ) : d*2^(j-m)≤d*2^j :=
    Nat.mul_le_mul_left d (Nat.pow_le_pow_right (by omega) (Nat.sub_le j m))
  choose p hpR hp hpB hpτ using (fun j => matrix_range_projection (d*2^j)
    (d*2^(j-m)) (hr j) (ρ j) τ (hτ j))
  apply coordinate_projection (fun j => (ρ j).range) τ h1 htr ω p hp hpR
  apply tendsto_const_nhds.congr'
  filter_upwards [hω (eventually_ge_atTop m)] with j hj
  exact ((hpτ j).trans (dyadic_rank_trace d m j hd hj)).symm

theorem matrix_ultra_diffuse (hd : 0<d) (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (htr : ∀ x y, τ (x*y)=τ (y*x)) (hinj : Function.Injective (gnsVector τ))
    (hρ : ∀ j, Function.Injective (ρ j))
    (hτ : ∀ j x, τ (ρ j x)=((d*2^j:ℕ):ℂ)⁻¹*Matrix.trace x)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤atTop) :
    IsDiffuse (gnsVonNeumann (coordinateTrace (fun j => (ρ j).range) τ ω)) := by
  exact factor_diffuse_of_dyadic_projections _ (matrixUltraNormalTrace d ρ τ h1 htr ω)
    (matrix_ultra_factor d ρ τ h1 htr hinj hρ ω hω)
    (matrix_ultra_projection d ρ hd τ h1 htr hτ ω hω)

end

end KKVariableUltra
end

end OAI

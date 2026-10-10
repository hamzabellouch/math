import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberHomCoordinates
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedMaps
import OAI.Algebra.AuslanderReiten.HomComplex.TensorFullHomZero

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex.HomComplex
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
local notation "τ₀" => AFrobeniusTrace k q
local notation "P₀" => A.simpleComplete q

abbrev fiberComplete := (evaluatedFiber q H₁ H₂).completeCochain τ₀

def fiberFullHomEquiv (n : ℤ) :
    CohomologyClass P₀ (fiberComplete q H₁ H₂) n ≃ₗ[k] FiberHom q H₁ H₂ n :=
  fullHomShiftedHomotopyEquiv k P₀ (fiberComplete q H₁ H₂) n

def simpleFullHomEquiv (n : ℤ) : CohomologyClass P₀ P₀ n ≃ₗ[k] SimpleHom q n :=
  fullHomShiftedHomotopyEquiv k P₀ P₀ n

def fiberFullRhoPair (n : ℤ) :
    CohomologyClass P₀ (fiberComplete q H₁ H₂) n →ₗ[k]
      (CohomologyClass P₀ P₀ n × CohomologyClass P₀ P₀ n) :=
  (((simpleFullHomEquiv q n).symm.prodCongr (simpleFullHomEquiv q n).symm).toLinearMap.comp
    (fiberHomRhoPair q H₁ H₂ n)).comp (fiberFullHomEquiv q H₁ H₂ n).toLinearMap

theorem fiberFullRhoPair_apply (n : ℤ)
    (x : CohomologyClass P₀ (fiberComplete q H₁ H₂) n) :
    fiberFullRhoPair q H₁ H₂ n x =
      (fullHomPostcomp (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₁ q H₁ H₂)) n x,
       fullHomPostcomp (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₂ q H₁ H₂)) n x) := by
  apply ((simpleFullHomEquiv q n).prodCongr (simpleFullHomEquiv q n)).injective
  simp only [fiberFullRhoPair, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.prodCongr_apply, LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · exact (fullHomShiftedHomotopyEquiv_postcomp k n
      (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₁ q H₁ H₂)) x).symm
  · exact (fullHomShiftedHomotopyEquiv_postcomp k n
      (FiniteLeftModule.resolutionMap τ₀ (evaluatedRho₂ q H₁ H₂)) x).symm

end ArExplicit.T

end

end OAI

import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalMaps
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleCoefficients
import Mathlib.Algebra.Homology.Additive

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ)
variable (T : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ)

abbrev complexTerm (n : ℤ) := RetainedBimodule k (L × R) (L × R)
  (OffDiagonal (BimoduleCoefficients k R L (O.X n)) (BimoduleCoefficients k L R (T.X n)))

def complexDifferential (n : ℤ) :=
  RetainedBimodule.map (k := k) (S := L × R) (A := L × R)
    (map (BimoduleCoefficients.map k R L (O.d n (n+1)))
      (BimoduleCoefficients.map k L R (T.d n (n+1))))
    (map_left (BimoduleCoefficients.map k R L (O.d n (n+1)))
      (BimoduleCoefficients.map_left k R L (O.d n (n+1)))
      (BimoduleCoefficients.map k L R (T.d n (n+1)))
      (BimoduleCoefficients.map_left k L R (T.d n (n+1))))

theorem complexDifferential_square (n : ℤ) :
    (complexDifferential k L R O T (n+1)).comp (complexDifferential k L R O T n) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · exact congrArg (fun f => f.hom x.1) (O.d_comp_d n (n+1) ((n+1)+1))
  · exact congrArg (fun f => f.hom x.2) (T.d_comp_d n (n+1) ((n+1)+1))

/-- Actual off-diagonal complex with both actions of the product algebra retained. -/
def complex : CochainComplex (ModuleCat.{u} ((L × R) ⊗[k] (L × R)ᵐᵒᵖ)) ℤ :=
  CochainComplex.of (fun n => ModuleCat.of _ (complexTerm k L R O T n))
    (fun n => ModuleCat.ofHom (complexDifferential k L R O T n))
    (fun n => ModuleCat.hom_ext (complexDifferential_square k L R O T n))
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI

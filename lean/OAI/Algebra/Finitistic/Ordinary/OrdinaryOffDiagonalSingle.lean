import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalObjects
import Mathlib.Algebra.Homology.Single

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) (T : ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ))

abbrev singles : CochainComplex (ModuleCat.{u} ((L × R) ⊗[k] (L × R)ᵐᵒᵖ)) ℤ :=
  complex k L R ((HomologicalComplex.single _ (.up ℤ) 0).obj O)
    ((HomologicalComplex.single _ (.up ℤ) 0).obj T)

theorem singles_isZero (n : ℤ) (hn : n ≠ 0) : IsZero ((singles k L R O T).X n) :=
  object_isZero k L R (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 O n hn)
    (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 T n hn)

def singleTermIso (n : ℤ) : (singles k L R O T).X n ≅
    ((HomologicalComplex.single _ (.up ℤ) 0).obj (object k L R O T)).X n := by
  by_cases hn : n = 0
  · subst n
    exact objectIso k L R (HomologicalComplex.singleObjXSelf (.up ℤ) 0 O)
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 T) ≪≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (object k L R O T)).symm
  · exact (singles_isZero k L R O T n hn).iso
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (object k L R O T) n hn)

/-- The off-diagonal direct sum of two ordinary modules is their ordinary bimodule in degree zero. -/
def singleIso : singles k L R O T ≅
    (HomologicalComplex.single _ (.up ℤ) 0).obj (object k L R O T) :=
  HomologicalComplex.Hom.isoOfComponents (singleTermIso k L R O T) (by
    intro n m h
    change n+1=m at h
    by_cases hn : n = 0
    · have hm : m ≠ 0 := by omega
      exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (object k L R O T) m hm).eq_of_tgt _ _
    · exact (singles_isZero k L R O T n hn).eq_of_src _ _)
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI

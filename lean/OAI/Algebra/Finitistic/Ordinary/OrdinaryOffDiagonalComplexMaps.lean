import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalComplex

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable {O O' : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ}
variable {T T' : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ}

def complexTermMap (f : O ⟶ O') (g : T ⟶ T') (n : ℤ) :=
  RetainedBimodule.map (k := k) (S := L × R) (A := L × R)
    (map (BimoduleCoefficients.map k R L (f.f n)) (BimoduleCoefficients.map k L R (g.f n)))
    (map_left (BimoduleCoefficients.map k R L (f.f n))
      (BimoduleCoefficients.map_left k R L (f.f n))
      (BimoduleCoefficients.map k L R (g.f n))
      (BimoduleCoefficients.map_left k L R (g.f n)))

theorem complex_d (n : ℤ) : (complex k L R O T).d n (n+1) =
    ModuleCat.ofHom (complexDifferential k L R O T n) :=
  CochainComplex.of_d (fun n => ModuleCat.of _ (complexTerm k L R O T n))
    (fun n => ModuleCat.ofHom (complexDifferential k L R O T n)) n

/-- An actual map of off-diagonal complexes retaining both product-ring actions. -/
def complexMap (f : O ⟶ O') (g : T ⟶ T') : complex k L R O T ⟶ complex k L R O' T' where
  f n := ModuleCat.ofHom (complexTermMap k L R f g n)
  comm' n m h := by
    change n+1=m at h
    subst m
    rw [complex_d,complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact congrArg (fun h => h.hom x.1) (f.comm n (n+1))
    · exact congrArg (fun h => h.hom x.2) (g.comm n (n+1))
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI

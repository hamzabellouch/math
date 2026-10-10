import OAI.Algebra.Finitistic.Ordinary.OrdinaryOffDiagonalComplexMaps
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRetainedRestriction
import OAI.Algebra.Finitistic.Ordinary.OrdinaryPairQuasiIso
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRestrictionHomology

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.OffDiagonal
universe u
variable (k L R : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable (O : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ)
variable (T : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ)

def forgetTermIso (n : ℤ) : (underlyingComplex (k := k) (complex k L R O T)).X n ≅
    (PairComplex.complex (underlyingComplex (k := k) O) (underlyingComplex (k := k) T)).X n :=
  (RetainedBimodule.scalarEquiv k (L × R) (L × R)
    (OffDiagonal (BimoduleCoefficients k R L (O.X n)) (BimoduleCoefficients k L R (T.X n)))).toModuleIso

/-- Forgetting the two outside actions gives the actual coordinate direct-sum complex. -/
def forgetIso : underlyingComplex (k := k) (complex k L R O T) ≅
    PairComplex.complex (underlyingComplex (k := k) O) (underlyingComplex (k := k) T) :=
  HomologicalComplex.Hom.isoOfComponents (forgetTermIso k L R O T) (by
    intro n m h
    change n+1=m at h
    subst m
    change (forgetTermIso k L R O T n).hom ≫ _ =
      (ModuleCat.restrictScalars (algebraMap k ((L × R) ⊗[k] (L × R)ᵐᵒᵖ))).map
        ((complex k L R O T).d n (n+1)) ≫ (forgetTermIso k L R O T (n+1)).hom
    rw [complex_d,PairComplex.complex_d]
    rfl)

variable {O T} {O' : CochainComplex (ModuleCat.{u} (R ⊗[k] Lᵐᵒᵖ)) ℤ}
variable {T' : CochainComplex (ModuleCat.{u} (L ⊗[k] Rᵐᵒᵖ)) ℤ}

theorem forgetIso_natural (f : O ⟶ O') (g : T ⟶ T') :
    ((ModuleCat.restrictScalars (algebraMap k ((L × R) ⊗[k] (L × R)ᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map
      (complexMap k L R f g) ≫ (forgetIso k L R O' T').hom =
    (forgetIso k L R O T).hom ≫ PairComplex.map
      (((ModuleCat.restrictScalars (algebraMap k (R ⊗[k] Lᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map f)
      (((ModuleCat.restrictScalars (algebraMap k (L ⊗[k] Rᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map g) := by
  ext n x
  rfl

/-- The actual off-diagonal map is a quasi-isomorphism when its two components are. -/
theorem complexMap_quasiIso (f : O ⟶ O') (g : T ⟶ T') [QuasiIso f] [QuasiIso g] :
    QuasiIso (complexMap k L R f g) := by
  apply (RestrictionHomology.quasiIso_iff (algebraMap k ((L × R) ⊗[k] (L × R)ᵐᵒᵖ)) _).mp
  let f' := ((ModuleCat.restrictScalars (algebraMap k (R ⊗[k] Lᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map f
  let g' := ((ModuleCat.restrictScalars (algebraMap k (L ⊗[k] Rᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map g
  have : QuasiIso f' := (RestrictionHomology.quasiIso_iff (algebraMap k (R ⊗[k] Lᵐᵒᵖ)) f).mpr inferInstance
  have : QuasiIso g' := (RestrictionHomology.quasiIso_iff (algebraMap k (L ⊗[k] Rᵐᵒᵖ)) g).mpr inferInstance
  have := PairComplex.map_quasiIso f' g'
  let h := ((ModuleCat.restrictScalars (algebraMap k ((L × R) ⊗[k] (L × R)ᵐᵒᵖ))).mapHomologicalComplex (.up ℤ)).map
    (complexMap k L R f g)
  have hh : QuasiIso (h ≫ (forgetIso k L R O' T').hom) := by
    dsimp only [h]
    rw [forgetIso_natural]
    exact inferInstanceAs (QuasiIso ((forgetIso k L R O T).hom ≫ PairComplex.map f' g'))
  exact (quasiIso_iff_comp_right h (forgetIso k L R O' T').hom).mp hh
end LittleFinitistic.OrdinarySimulation.OffDiagonal

end

end OAI

import OAI.Algebra.Finitistic.Dimension.PDSquareZeroResidue
import OAI.Algebra.Finitistic.Dimension.PDResidueRing
import OAI.Algebra.Finitistic.Dimension.PDTor
import OAI.Algebra.Finitistic.Tensor.BalancedTensorMaps

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.PDResidueProjection
universe u
variable {k A D : Type u} [Field k] [Ring A] [Algebra k A] [Ring D] [Algebra k D]
variable (f : A →ₐ[k] D) (hf : Function.Surjective f)
variable (hsq : ∀ a ∈ RingHom.ker f.toRingHom, ∀ b ∈ RingHom.ker f.toRingHom, a*b=0)

def InflatedResidue (_f : A →ₐ[k] D) := PDTensor.Residue (A := D)
instance : AddCommGroup (InflatedResidue f) := inferInstanceAs (AddCommGroup (PDTensor.Residue (A := D)))
instance : Module k (InflatedResidue f) := inferInstanceAs (Module k (PDTensor.Residue (A := D)))
instance : Module Aᵐᵒᵖ (InflatedResidue f) :=
  Module.compHom (PDTensor.Residue (A := D)) f.toRingHom.op
instance (priority := 50) : Module Dᵐᵒᵖ (InflatedResidue f) :=
  inferInstanceAs (Module Dᵐᵒᵖ (PDTensor.Residue (A := D)))
instance (priority := 50) : IsScalarTower k Dᵐᵒᵖ (InflatedResidue f) :=
  inferInstanceAs (IsScalarTower k Dᵐᵒᵖ (PDTensor.Residue (A := D)))
instance : IsScalarTower k Aᵐᵒᵖ (InflatedResidue f) where
  smul_assoc c a s := by
    change MulOpposite.op (f (c • a.unop)) • (s : PDTensor.Residue (A := D)) =
      c • (MulOpposite.op (f a.unop) • (s : PDTensor.Residue (A := D)))
    rw [map_smul, MulOpposite.op_smul, smul_assoc]

def map : PDTensor.Residue (A := A) →ₗ[k] InflatedResidue f :=
  ((PDTensor.rightRadical (A := A)).restrictScalars k).liftQ
    (((PDTensor.rightRadical (A := D)).restrictScalars k).mkQ.comp f.toLinearMap) (by
      intro a ha
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      have he := PDSquareZero.comap_jacobson f.toRingHom hf hsq
      change a ∈ Ring.jacobson A at ha
      rw [← he] at ha
      exact ha)

@[simp] theorem map_mk (a : A) : map f hf hsq (Submodule.Quotient.mk a) =
    (Submodule.Quotient.mk (f a) : PDTensor.Residue (A := D)) := rfl

/-- The radical quotient-ring comparison also respects the actual k action. -/
def equiv : PDTensor.Residue (A := A) ≃ₗ[k] InflatedResidue f :=
  LinearEquiv.ofBijective (map f hf hsq) (by
    have he : (fun s => map f hf hsq s) =
        (fun s => PDSquareZero.residueQuotientEquiv f.toRingHom hf hsq s) := by
      funext s
      induction s using Submodule.Quotient.induction_on with
      | _ a => exact (PDSquareZero.residueQuotientEquiv_mk f.toRingHom hf hsq a).symm
    change Function.Bijective (fun s => map f hf hsq s)
    rw [he]
    exact (PDSquareZero.residueQuotientEquiv f.toRingHom hf hsq).bijective)

/-- Its right A action is precisely restriction through the canonical projection. -/
def rightEquiv : PDTensor.Residue (A := A) ≃ₗ[Aᵐᵒᵖ] InflatedResidue f where
  __ := (equiv f hf hsq).toAddEquiv
  map_smul' a s := by
    induction s using Submodule.Quotient.induction_on with
    | _ b =>
      change (Submodule.Quotient.mk (f (b*a.unop)) : PDTensor.Residue (A := D)) =
        Submodule.Quotient.mk (f b * f a.unop)
      rw [map_mul]

variable (N : Type u) [AddCommGroup N] [Module k N] [Module A N]

def tensorEquiv : BalancedTensor.Tensor k A (PDTensor.Residue (A := A)) N ≃ₗ[k]
    BalancedTensor.Tensor k A (InflatedResidue f) N :=
  LinearEquiv.ofLinearMap
    (BalancedTensor.mapLeft (k := k) N (rightEquiv f hf hsq).toLinearMap)
    (BalancedTensor.mapLeft (k := k) N (rightEquiv f hf hsq).symm.toLinearMap)
    (by
      apply BalancedTensor.ext
      intro s n
      simp only [LinearMap.comp_apply, BalancedTensor.mapLeft_mk, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply])
    (by
      apply BalancedTensor.ext
      intro s n
      simp only [LinearMap.comp_apply, BalancedTensor.mapLeft_mk, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.id_apply])

/-- The residue projection comparison is natural on all actual left A-modules. -/
def tensorNatIso : PDTensor.tensorFunctor k A (PDTensor.Residue (A := A)) ≅
    PDTensor.tensorFunctor k A (InflatedResidue f) :=
  NatIso.ofComponents (fun M => (tensorEquiv f hf hsq (PDTensor.ScalarModule k A M)).toModuleIso)
    (by
      intro M L h
      apply ModuleCat.hom_ext
      apply BalancedTensor.ext
      intro s n
      rfl)

variable (M : ModuleCat.{u} A) (P : ProjectiveResolution M)
def resolutionIso :
    ((PDTensor.tensorFunctor k A (PDTensor.Residue (A := A))).mapHomologicalComplex _).obj P.complex ≅
    ((PDTensor.tensorFunctor k A (InflatedResidue f)).mapHomologicalComplex _).obj P.complex :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (tensorNatIso f hf hsq).app (P.complex.X n))
    (fun i j _ => ((tensorNatIso f hf hsq).hom.naturality (P.complex.d i j)).symm)

/-- Actual derived residue tensor is unchanged by the proved right-module identification. -/
def torIso (n : ℕ) : PDTensor.Tor (k := k) (PDTensor.Residue (A := A)) M n ≅
    PDTensor.Tor (k := k) (InflatedResidue f) M n :=
  P.isoLeftDerivedObj (PDTensor.tensorFunctor k A (PDTensor.Residue (A := A))) n ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (resolutionIso f hf hsq M P) ≪≫
    (P.isoLeftDerivedObj (PDTensor.tensorFunctor k A (InflatedResidue f)) n).symm
end LittleFinitistic.PDResidueProjection

end

end OAI

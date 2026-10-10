import OAI.Algebra.Finitistic.Ordinary.OrdinaryConeQuasiIso
import Mathlib.Algebra.Category.ModuleCat.Biproducts

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.ConeCoordinates
universe u
variable {R : Type u} [Ring R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)

/-- The native cone term in its actual two module coordinates. -/
def coordinateIso (n : ℤ) : (CochainComplex.mappingCone f).X n ≅
    ModuleCat.of R (K.X (n+1) × L.X n) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n+1) rfl ≪≫
    ModuleCat.biprodIsoProd (K.X (n+1)) (L.X n)

def coordinateEquiv (n : ℤ) : (CochainComplex.mappingCone f).X n ≃ₗ[R] (K.X (n+1) × L.X n) :=
  (coordinateIso f n).toLinearEquiv

theorem coordinate_fst (n : ℤ) :
    (coordinateIso f n).hom ≫ ModuleCat.ofHom (LinearMap.fst R (K.X (n+1)) (L.X n)) =
      HomologicalComplex.homotopyCofiber.fstX f n (n+1) rfl := by
  unfold coordinateIso
  erw [Iso.trans_hom,Category.assoc,← ModuleCat.biprodIsoProd_inv_comp_fst,Iso.hom_inv_id_assoc]
  rfl

theorem coordinate_snd (n : ℤ) :
    (coordinateIso f n).hom ≫ ModuleCat.ofHom (LinearMap.snd R (K.X (n+1)) (L.X n)) =
      HomologicalComplex.homotopyCofiber.sndX f n := by
  unfold coordinateIso
  erw [Iso.trans_hom,Category.assoc,← ModuleCat.biprodIsoProd_inv_comp_snd,Iso.hom_inv_id_assoc]
  apply HomologicalComplex.homotopyCofiber.ext_from_X f (n+1) n rfl
  · erw [← Category.assoc, HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom,
      biprod.inl_snd, HomologicalComplex.homotopyCofiber.inlX_sndX]
  · erw [← Category.assoc, HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom,
      biprod.inr_snd, HomologicalComplex.homotopyCofiber.inrX_sndX]

/-- The first coordinate of the native cone differential carries its negative sign. -/
theorem differential_fst (n : ℤ) (z : (CochainComplex.mappingCone f).X n) :
    (coordinateEquiv f (n+1) (((CochainComplex.mappingCone f).d n (n+1)).hom z)).1 =
      -((K.d (n+1) ((n+1)+1)).hom (coordinateEquiv f n z).1) := by
  have hh := HomologicalComplex.homotopyCofiber.d_fstX f n (n+1) ((n+1)+1) rfl rfl
  rw [← coordinate_fst,← coordinate_fst] at hh
  exact congrArg (fun g => g.hom z) hh

/-- The second coordinate contains the input map and the target differential. -/
theorem differential_snd (n : ℤ) (z : (CochainComplex.mappingCone f).X n) :
    (coordinateEquiv f (n+1) (((CochainComplex.mappingCone f).d n (n+1)).hom z)).2 =
      (f.f (n+1)).hom (coordinateEquiv f n z).1 +
      (L.d n (n+1)).hom (coordinateEquiv f n z).2 := by
  have hh := HomologicalComplex.homotopyCofiber.d_sndX f n (n+1) rfl
  rw [← coordinate_snd,← coordinate_snd,← coordinate_fst] at hh
  exact congrArg (fun g => g.hom z) hh
end LittleFinitistic.ConeCoordinates

end

end OAI

import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Model
import OAI.AlgebraicGeometry.Seshadri.Geometry.FiniteScheme
import OAI.AlgebraicGeometry.Seshadri.Cohomology.AffineVanishing

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Abelian Opposite

variable {X : Scheme}

def globalHomLinearEquiv (M : X.Modules) :
    GlobalSections X M ≃ₗ[Γ(X,⊤)] Γ(M,⊤) where
  toEquiv := FlasqueCohomology.globalHomEquiv X.ringCatSheaf M
  map_add' := by intro f g; rfl
  map_smul' := by
    intro r f
    change restrictScalar X ⊤ r • f.app ⊤ (1 : Γ(X,⊤)) = r • f.app ⊤ (1 : Γ(X,⊤))
    congr 1
    change (X.presheaf.map (𝟙 (op ⊤))) r = r
    rw [X.presheaf.map_id]
    rfl

def cohomologyZeroSections (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    let _ : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
    let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
    cohomology M 0 ≃ₗ[ℂ] Γ(M,⊤) := by
  dsimp only
  letI : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
  letI : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
  let e := (Ext.linearEquiv₀ (R := Γ(X,⊤)) (X := structureSheaf X) (Y := M)).trans
    (globalHomLinearEquiv M)
  exact { e.toAddEquiv with map_smul' := fun r x => e.map_smul (baseScalars f r) x }

lemma cohomologyDimension_zero (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    cohomologyDimension f M 0 =
      let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
      Module.finrank ℂ Γ(M,⊤) := by
  let : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
  let : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
  exact (cohomologyZeroSections f M).finrank_eq

theorem affine_eulerCharacteristic (f : X ⟶ Spec (CommRingCat.of ℂ))
    [IsAffine X] [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent] (d : ℕ) :
    eulerCharacteristic f d M =
      let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
      (Module.finrank ℂ Γ(M,⊤) : ℤ) := by
  unfold eulerCharacteristic
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, cohomologyDimension_zero]
  · intro n hn hn0
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have : Subsingleton (cohomology M (m+1)) :=
      ⟨fun x y => (AffineSchemeCohomology.affine_ext_zero X M m x).trans
        (AffineSchemeCohomology.affine_ext_zero X M m y).symm⟩
    simp [cohomologyDimension, Module.finrank_zero_of_subsingleton]
  · simp

theorem proper_finite_euler (f : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper f] [Finite X] (d : ℕ) :
    eulerCharacteristic f d (structureSheaf X) =
      let _ : Algebra ℂ Γ(X,⊤) := (baseScalars f).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  let : (structureSheaf X).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (CategoryTheory.Limits.coproductUniqueIso
        (fun (_ : PUnit) => SheafOfModules.unit X.ringCatSheaf))
      (inferInstanceAs (SheafOfModules.free (R := X.ringCatSheaf) PUnit).IsQuasicoherent)
  exact affine_eulerCharacteristic f (structureSheaf X) d

end
end MaximalSeshadri.Geometry
end


end
end

end OAI

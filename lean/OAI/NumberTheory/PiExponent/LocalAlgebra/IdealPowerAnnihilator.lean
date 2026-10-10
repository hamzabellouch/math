import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerFiltration

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem hom_ext_affine {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ U : X.affineOpens, f.app U.1 = g.app U.1) : f = g := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  apply F.map_injective
  apply Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ (show Opens.IsBasis
    (Set.range (fun U : X.affineOpens => U.1)) by simpa using X.isBasis_affineOpens)
  intro U
  ext x
  exact ConcreteCategory.congr_hom (h U) x

lemma restriction_mem_ideal (I : X.IdealSheafData) (r : Γ(X,⊤))
    (hr : I.subschemeι.appTop r = 0) (U : X.affineOpens) :
    restrictScalar X U.1 r ∈ I.ideal U := by
  rw [← I.ker_subschemeι_app U, RingHom.mem_ker]
  unfold restrictScalar
  have h := congrArg (fun f => f r) (I.subschemeι.naturality
    (homOfLE (show U.1 ≤ ⊤ from le_top)).op)
  change I.subschemeι.app U.1 (X.presheaf.map (homOfLE le_top).op r) = _ at h
  rw [CommRingCat.comp_apply] at h
  exact h.trans ((congrArg _ hr).trans (map_zero _))

lemma smul_closedInclusion_structureMap_eq_zero (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    (r • closedInclusion (I^n)) ≫ structureMap (I^(n+1)).subschemeι = 0 := by
  apply hom_ext_affine
  intro U
  ext x
  change (I^(n+1)).subschemeι.app U.1
    (restrictScalar X U.1 r * (show Γ(X,U.1) from (closedInclusion (I^n)).app U.1 x)) = 0
  apply RingHom.mem_ker.mp
  rw [(I^(n+1)).ker_subschemeι_app U]
  change restrictScalar X U.1 r * (show Γ(X,U.1) from (closedInclusion (I^n)).app U.1 x) ∈
    I.ideal U ^ (n+1)
  rw [pow_succ']
  apply Ideal.mul_mem_mul (restriction_mem_ideal I r hr U)
  change (closedInclusion (I^n)).app U.1 x ∈ (I^n).ideal U
  rw [← closed_image (I^n) U]
  exact ⟨x,rfl⟩

def multiplyToNextPower (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    closedModule (I^n) ⟶ closedModule (I^(n+1)) :=
  kernel.lift (structureMap (I^(n+1)).subschemeι) (r • closedInclusion (I^n))
    (smul_closedInclusion_structureMap_eq_zero I n r hr)

@[reassoc (attr := simp)] lemma multiplyToNextPower_inclusion (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    multiplyToNextPower I n r hr ≫ closedInclusion (I^(n+1)) = r • closedInclusion (I^n) :=
  kernel.lift_ι _ _ _

lemma multiplyToNextPower_powerMap (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    multiplyToNextPower I n r hr ≫ powerMap I n = r • 𝟙 (closedModule (I^n)) := by
  apply (cancel_mono (closedInclusion (I^n))).mp
  rw [Category.assoc, show powerMap I n ≫ closedInclusion (I^n) =
    closedInclusion (I^(n+1)) from closedMap_inclusion _]
  rw [multiplyToNextPower_inclusion]
  ext U x
  change restrictScalar X U r * (show Γ(X,U) from (closedInclusion (I^n)).app U x) =
    (closedInclusion (I^n)).app U (restrictScalar X U r • x)
  exact ((closedInclusion (I^n)).app_smul _ x).symm

theorem powerLayer_smul_id_eq_zero (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    r • 𝟙 (powerLayer I n) = 0 := by
  apply (cancel_epi (cokernel.π (powerMap I n))).mp
  have h : (r • 𝟙 (closedModule (I^n))) ≫ cokernel.π (powerMap I n) = 0 := by
    rw [← multiplyToNextPower_powerMap I n r hr, Category.assoc, cokernel.condition,
      Limits.comp_zero]
  calc
    _ = (r • 𝟙 (closedModule (I^n))) ≫ cokernel.π (powerMap I n) := by
      ext U x
      exact ((cokernel.π (powerMap I n)).app_smul _ x).symm
    _ = 0 := h
    _ = _ := Limits.comp_zero.symm
end
end PiExponentSeshadri.IdealModule

end OAI

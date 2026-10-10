import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.PolygonCoefficientFinite

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section NoetherianTor
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe nt

namespace NoetherianResolution
variable {R : Type nt} [CommRing R]

theorem homologyMap_smul {C D : ChainComplex (ModuleCat.{nt} R) ℕ}
    (f : C ⟶ D) (r : R) (n : ℕ) :
    HomologicalComplex.homologyMap (r • f) n =
      r • HomologicalComplex.homologyMap f n := by
  exact ShortComplex.homologyMap_smul
    ((HomologicalComplex.shortComplexFunctor (ModuleCat R) _ n).map f) r

noncomputable def annihilatorHomotopy {M : ModuleCat.{nt} R}
    (P : ProjectiveResolution M) (r : R) (hr : ∀ x : M, r • x = 0) :
    Homotopy (r • 𝟙 P.complex) 0 := by
  apply ProjectiveResolution.liftHomotopyZero
  apply HomologicalComplex.to_single_hom_ext
  ext x
  change (P.π.f 0).hom (r • x) = 0
  rw [map_smul]
  exact hr (P.π.f 0 x)

theorem annihilator_homology {M : ModuleCat.{nt} R}
    (P : ProjectiveResolution M) (F : ModuleCat.{nt} R ⥤ ModuleCat.{nt} R)
    [F.Additive] [Functor.Linear R F] (r : R) (hr : ∀ x : M, r • x = 0)
    (n : ℕ) (x : ((F.mapHomologicalComplex _).obj P.complex).homology n) :
    r • x = 0 := by
  have h := (F.mapHomotopy (annihilatorHomotopy P r hr)).homologyMap_eq n
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero,
    homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) x

variable [IsNoetherianRing R]

theorem finite_tensor_resolution_homology (L M : FGModuleCat.{nt} R) (n : ℕ) :
    Module.Finite R
      (((((tensoringLeft (ModuleCat R)).obj L.obj).mapHomologicalComplex _).obj
        (resolution M).complex).homology n) := by
  have : Module.Finite R
      (((((tensoringLeft (ModuleCat R)).obj L.obj).mapHomologicalComplex _).obj
        (resolution M).complex).X n) :=
    Module.Finite.tensorProduct R L ((resolution M).complex.X n)
  exact finite_homology _ n

end NoetherianResolution

theorem module_finite_int_of_augmentation {R : Type*} [Ring R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ε : R →+* ℤ) (h : ∀ (r : R) (x : M), r • x = ε r • x) :
    Module.Finite ℤ M := by
  obtain ⟨s,hs⟩ := (Module.Finite.fg_top (R := R) (M := M))
  refine ⟨s, ?_⟩
  apply top_unique
  intro x hx
  have hx' : x ∈ Submodule.span R (s : Set M) := by rw [hs]; trivial
  clear hx
  induction hx' using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [h]; exact Submodule.smul_mem _ _ hx

end NoetherianTor

section AugmentationTor
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace NoetherianResolution
variable {R : Type} [CommRing R] [IsNoetherianRing R]

noncomputable abbrev augmentationModule (ε : R →+* ℤ) : ModuleCat R :=
  (ModuleCat.restrictScalars ε).obj (ModuleCat.of ℤ ℤ)

instance finite_augmentationModule (ε : R →+* ℤ) :
    Module.Finite R (augmentationModule ε) := by
  have : Module.Finite ℤ (augmentationModule ε) := inferInstanceAs (Module.Finite ℤ ℤ)
  exact Module.Finite.of_restrictScalars_finite ℤ R (augmentationModule ε)

noncomputable def augmentationResolution (ε : R →+* ℤ) :
    ProjectiveResolution (augmentationModule ε) :=
  resolution (FGModuleCat.of R (augmentationModule ε))

noncomputable def augmentationComplex (ε : R →+* ℤ) (L : FGModuleCat R) :
    ChainComplex (ModuleCat R) ℕ :=
  ((((tensoringLeft (ModuleCat R)).obj L.obj).mapHomologicalComplex _).obj
    (augmentationResolution ε).complex)

instance finite_augmentation_homology (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ) :
    Module.Finite R ((augmentationComplex ε L).homology n) :=
  finite_tensor_resolution_homology L (FGModuleCat.of R (augmentationModule ε)) n

theorem augmentation_homology_smul (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ)
    (r : R) (x : (augmentationComplex ε L).homology n) :
    r • x = ε r • x := by
  have h0 : ∀ z : augmentationModule ε, (r - (ε r : R)) • z = 0 := by
    intro z
    change ε (r - (ε r : R)) • z = 0
    simp only [map_sub, map_intCast, Int.cast_id, sub_self, zero_smul]
  have h := annihilator_homology (augmentationResolution ε)
    ((tensoringLeft (ModuleCat R)).obj L.obj) (r - (ε r : R)) h0 n x
  have h' : (r - (ε r : R)) • x = 0 := h
  rw [sub_smul, sub_eq_zero] at h'
  simpa only [Int.cast_smul_eq_zsmul] using h'

theorem finite_int_augmentation_homology (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ) :
    Module.Finite ℤ ((augmentationComplex ε L).homology n) :=
  module_finite_int_of_augmentation ε (augmentation_homology_smul ε L n)

theorem finite_int_Tor_augmentation (ε : R →+* ℤ) (L : FGModuleCat R) (n : ℕ) :
    Module.Finite ℤ (((Tor (ModuleCat R) n).obj L.obj).obj (augmentationModule ε)) := by
  have := finite_int_augmentation_homology ε L n
  let e : (((Tor (ModuleCat R) n).obj L.obj).obj (augmentationModule ε)) ≅
      (augmentationComplex ε L).homology n :=
    (augmentationResolution ε).isoLeftDerivedObj
    ((tensoringLeft (ModuleCat R)).obj L.obj) n
  exact Module.Finite.of_surjective (e.inv.hom.restrictScalars ℤ)
    e.toLinearEquiv.symm.surjective

end NoetherianResolution
end AugmentationTor

section RingCoinvariants

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
attribute [local instance 1200] Rep.hV2
namespace RingCoinvariants
variable {G : Type} [CommGroup G]
local notation "R" => MonoidAlgebra ℤ G

noncomputable abbrev inverseRep (M : ModuleCat R) : Rep ℤ G :=
  Rep.of ((Representation.ofModule' (k := ℤ) (G := G) M).comp (invMonoidHom : G →* G))

noncomputable abbrev moduleRep (M : ModuleCat R) : Rep ℤ G :=
  Rep.of (Representation.ofModule' (k := ℤ) (G := G) M)

@[simp] theorem inverseRep_apply (M : ModuleCat R) (g : G) (x : M) :
    (inverseRep M).ρ g x = (MonoidAlgebra.single g⁻¹ 1 : R) • x := rfl

@[simp] theorem moduleRep_apply (M : ModuleCat R) (g : G) (x : M) :
    (moduleRep M).ρ g x = (MonoidAlgebra.single g 1 : R) • x := rfl

noncomputable def forwardTensor (L M : ModuleCat R) :
    (↑(inverseRep L) ⊗[ℤ] ↑(moduleRep M)) →ₗ[ℤ] (L ⊗[R] M) :=
  TensorProduct.lift ((TensorProduct.mk R L M).restrictScalars₁₂ ℤ ℤ)

theorem forwardTensor_invariant (L M : ModuleCat R) (g : G) :
    (forwardTensor L M).comp ((inverseRep L).ρ.tprod (moduleRep M).ρ g) =
      forwardTensor L M := by
  apply TensorProduct.ext
  ext x y
  change ((MonoidAlgebra.single g⁻¹ 1 : R) • x) ⊗ₜ[R]
    ((MonoidAlgebra.single g 1 : R) • y) = x ⊗ₜ[R] y
  rw [TensorProduct.smul_tmul, ← smul_assoc]
  simp [MonoidAlgebra.single_mul_single, ← MonoidAlgebra.one_def]

noncomputable def forward (L M : ModuleCat R) :
    ((Rep.coinvariantsTensor ℤ G).obj (inverseRep L)).obj (moduleRep M) →ₗ[ℤ]
      (L ⊗[R] M) :=
  Representation.Coinvariants.lift _ (forwardTensor L M)
    (forwardTensor_invariant L M)

@[simp] theorem forward_mk (L M : ModuleCat R) (x : L) (y : M) :
    forward L M (Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M) x y) =
      x ⊗ₜ[R] y := rfl

theorem mk_act_left {k H : Type} [CommRing k] [Group H] (A B : Rep k H)
    (g : H) (x : A) (y : B) :
    Rep.coinvariantsTensorMk A B (A.ρ g⁻¹ x) y =
      Rep.coinvariantsTensorMk A B x (B.ρ g y) := by
  have h := Representation.Coinvariants.mk_self_apply (A.ρ.tprod B.ρ) g
    ((A.ρ g⁻¹ x) ⊗ₜ[k] y)
  change Representation.Coinvariants.mk _
    ((A.ρ g (A.ρ g⁻¹ x)) ⊗ₜ[k] (B.ρ g y)) = _ at h
  have hx : A.ρ g (A.ρ g⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hx] at h
  exact h.symm

theorem mk_balanced_group (L M : ModuleCat R) (g : G) (x : L) (y : M) :
    Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M)
      ((MonoidAlgebra.single g 1 : R) • x) y =
    Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M)
      x ((MonoidAlgebra.single g 1 : R) • y) := by
  have h := mk_act_left (inverseRep L) (moduleRep M) g x y
  change Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M)
    ((MonoidAlgebra.single (g⁻¹)⁻¹ 1 : R) • x) y =
    Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M)
    x ((MonoidAlgebra.single g 1 : R) • y) at h
  simpa only [inv_inv] using h

noncomputable def backward (L M : ModuleCat R) :
    (L ⊗[R] M) →ₗ[ℤ]
      ((Rep.coinvariantsTensor ℤ G).obj (inverseRep L)).obj (moduleRep M) :=
  (TensorProduct.liftAddHom
    (LinearMap.toAddMonoidHom'.comp
      (Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M)).toAddMonoidHom)
    (by
      intro r x y
      induction r using MonoidAlgebra.induction_on with
      | of g => exact mk_balanced_group L M g x y
      | add r s hr hs => simpa only [add_smul, map_add, LinearMap.add_apply, AddMonoidHom.add_apply] using congrArg₂ (· + ·) hr hs
      | smul n r hr =>
        simpa only [smul_assoc, map_zsmul, AddMonoidHom.zsmul_apply] using congrArg (n • ·) hr
    )).toIntLinearMap

@[simp] theorem backward_mk (L M : ModuleCat R) (x : L) (y : M) :
    backward L M (x ⊗ₜ[R] y) =
      Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M) x y := rfl

noncomputable def equiv (L M : ModuleCat R) :
    ((Rep.coinvariantsTensor ℤ G).obj (inverseRep L)).obj (moduleRep M) ≃ₗ[ℤ]
      (L ⊗[R] M) := by
  refine LinearEquiv.ofLinearMap (forward L M) (backward L M) ?_ ?_
  · apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y => rfl
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · apply Representation.Coinvariants.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

@[simp] theorem equiv_mk (L M : ModuleCat R) (x : L) (y : M) :
    equiv L M (Rep.coinvariantsTensorMk (inverseRep L) (moduleRep M) x y) =
      x ⊗ₜ[R] y := rfl

noncomputable def moduleRepIso (M : ModuleCat R) :
    moduleRep M ≅ Rep.ofModuleMonoidAlgebra.obj M :=
  @Rep.mkIso ℤ G _ _ (moduleRep M) (Rep.ofModuleMonoidAlgebra.obj M) _ _
    (moduleRep M).hV2 (Rep.ofModuleMonoidAlgebra.obj M).hV2 _ _ {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun n x => by
      change n • x = (algebraMap ℤ R n) • x
      exact (IsScalarTower.algebraMap_smul R n x).symm
    isIntertwining' := fun g => rfl }

noncomputable def intRestrictionIso {S : Type} [Ring S] (M : ModuleCat S) :
    ModuleCat.of ℤ M ≅ (ModuleCat.restrictScalars (Int.castRingHom S)).obj M := by
  let A := ModuleCat.of ℤ M
  let B := (ModuleCat.restrictScalars (Int.castRingHom S)).obj M
  let e : A ≃ₗ[ℤ] B := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun integer element => by
      change integer • element = (integer : S) • (show M from element)
      exact (Int.cast_smul_eq_zsmul S integer (show M from element)).symm }
  exact e.toModuleIso

noncomputable def functorIso (L : ModuleCat R) :
    Rep.ofModuleMonoidAlgebra ⋙ (Rep.coinvariantsTensor ℤ G).obj (inverseRep L) ≅
      (tensoringLeft (ModuleCat R)).obj L ⋙
        ModuleCat.restrictScalars (Int.castRingHom R) :=
  NatIso.ofComponents (fun M =>
    (((Rep.coinvariantsTensor ℤ G).obj (inverseRep L)).mapIso (moduleRepIso M)).symm ≪≫
      (equiv L M).toModuleIso ≪≫ intRestrictionIso (ModuleCat.of R (L ⊗[R] M))) (by
    intro M N f
    apply Rep.coinvariantsTensor_hom_ext
    apply DFunLike.ext
    intro x
    apply DFunLike.ext
    intro y
    rfl)
end RingCoinvariants
end RingCoinvariants

end SimpleAmenable
end
end

end OAI

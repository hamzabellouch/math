import Mathlib
import OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros

namespace OAI

noncomputable section

namespace PiExponentSeshadri.FiniteSupport

section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
lemma discrete_restriction_surjective {X : TopCat.{0}} [DiscreteTopology X]
    (F : X.Sheaf AddCommGrpCat.{0}) {U V : Opens X} (i : V ⟶ U) :
    Function.Surjective (F.obj.map i.op) := by
  classical
  intro s
  let W : Opens X := ⟨(U : Set X) \ V, isOpen_discrete _⟩
  let D : Bool → Opens X := fun b => if b then V else W
  let e : ∀ b, D b ⟶ U := fun b => homOfLE (by
    cases b
    · exact fun x hx => hx.1
    · exact i.le)
  have hcover : U ≤ ⨆ b, D b := by
    intro x hx
    by_cases hV : x ∈ V
    · exact Opens.mem_iSup.mpr ⟨true,hV⟩
    · exact Opens.mem_iSup.mpr ⟨false,hx,hV⟩
  let t : ∀ b, F.obj.obj (op (D b)) := fun b => match b with
    | true => s
    | false => 0
  have hc : TopCat.Presheaf.IsCompatible F.obj D t := by
    intro b c
    cases b <;> cases c
    · rfl
    · have h : D false ⊓ D true = ⊥ := by
        ext x
        change ((x ∈ U ∧ x ∉ V) ∧ x ∈ V) ↔ False
        tauto
      let : Subsingleton (F.obj.obj (op (D false ⊓ D true))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty h).isZero
      exact Subsingleton.elim _ _
    · have h : D true ⊓ D false = ⊥ := by
        ext x
        change (x ∈ V ∧ x ∈ U ∧ x ∉ V) ↔ False
        tauto
      let : Subsingleton (F.obj.obj (op (D true ⊓ D false))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty h).isZero
      exact Subsingleton.elim _ _
    · rfl
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' D U e hcover t hc
  exact ⟨a,ha true⟩

lemma discrete_flasque {X : TopCat.{0}} [DiscreteTopology X]
    (F : X.Sheaf AddCommGrpCat.{0}) : F.IsFlasque where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (discrete_restriction_surjective F i.unop)

variable {X Y : Scheme.{0}}

lemma proper_finite_discrete (p : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper p] [Finite X] : DiscreteTopology X := by
  let : IsFinite p := Geometry.proper_finite_scheme_isFinite p
  have he : p ⁻¹' ({⟨⊥, Ideal.isPrime_bot⟩} : Set (Spec (CommRingCat.of ℂ))) = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have h := p.isDiscrete_preimage_singleton (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  rw [he] at h
  exact isDiscrete_univ_iff.mp h

lemma pushforward_flasque (f : X ⟶ Y) [DiscreteTopology X] (M : X.Modules) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
      ((Scheme.Modules.pushforward f).obj M)) where
  epi i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact discrete_restriction_surjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      ((Opens.map f.base).map i.unop)

theorem finite_pushforward_ext_zero (p : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper p] [Finite X] (f : X ⟶ Y) (M : X.Modules) (n : ℕ)
    (z : Geometry.cohomology ((Scheme.Modules.pushforward f).obj M) (n+1)) : z = 0 := by
  let : DiscreteTopology X := proper_finite_discrete p
  let := pushforward_flasque f M
  exact FlasqueCohomology.flasque_ext_zero Y.ringCatSheaf n _ z

def pushforwardUnitSections (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of ℂ)) :
    let _ : Module ℂ Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) :=
      Module.compHom _ (Geometry.baseScalars g)
    let _ : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
    Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) ≃ₗ[ℂ] Γ(X,⊤) := by
  dsimp only
  letI : Module ℂ Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) :=
    Module.compHom _ (Geometry.baseScalars g)
  letI : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
  refine { Equiv.refl _ with map_add' := fun _ _ => rfl, map_smul' := ?_ }
  intro r a
  change Γ(X,⊤) at a
  change (f.appTop) (Geometry.baseScalars g r) * a = Geometry.baseScalars (f ≫ g) r * a
  congr 1

theorem finite_pushforward_euler (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of ℂ))
    [IsProper (f ≫ g)] [Finite X] (d : ℕ) :
    Geometry.eulerCharacteristic g d
      ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X)) =
      let _ : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  let M := (Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X)
  unfold Geometry.eulerCharacteristic
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, Geometry.cohomologyDimension_zero]
    let : Module ℂ Γ(M,⊤) := Module.compHom _ (Geometry.baseScalars g)
    let : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
    exact_mod_cast (pushforwardUnitSections f g).finrank_eq
  · intro n hn hn0
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have : Subsingleton (Geometry.cohomology M (m+1)) :=
      ⟨fun x y => (finite_pushforward_ext_zero (f ≫ g) f _ m x).trans
        (finite_pushforward_ext_zero (f ≫ g) f _ m y).symm⟩
    simp [Geometry.cohomologyDimension, Module.finrank_zero_of_subsingleton]
  · simp

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem finite_pushforward_finiteDimensional (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X] (n : ℕ) :
    let M := (Scheme.Modules.pushforward f).obj (structureSheaf X)
    let _ := Module.compHom (cohomology M n) (baseScalars g)
    FiniteDimensional ℂ (cohomology M n) := by
  let M := (Scheme.Modules.pushforward f).obj (structureSheaf X)
  let := Module.compHom (cohomology M n) (baseScalars g)
  cases n with
  | zero =>
    let : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars g)
    let : Algebra ℂ Γ(X,⊤) := (baseScalars (f ≫ g)).toAlgebra
    let : FiniteDimensional ℂ Γ(X,⊤) := proper_finite_functions (f ≫ g)
    let e := (cohomologyZeroSections g M).trans (pushforwardUnitSections f g)
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  | succ n =>
    let : Subsingleton (cohomology M (n+1)) :=
      ⟨fun x y => (finite_pushforward_ext_zero (f ≫ g) f _ n x).trans
        (finite_pushforward_ext_zero (f ≫ g) f _ n y).symm⟩
    infer_instance

end PiExponentSeshadri.FiniteSupport

end

end OAI

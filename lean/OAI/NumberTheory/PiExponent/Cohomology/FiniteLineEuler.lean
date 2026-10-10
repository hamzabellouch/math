import Mathlib
import OAI.NumberTheory.PiExponent.Cohomology.CohomologyIso
import OAI.NumberTheory.PiExponent.Cohomology.FiniteSupportCohomology

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}}

def overFrame {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm)
end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.FiniteSupport

section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [DiscreteTopology X]

def pointOpen (x : X) : X.Opens := ⟨{x}, isOpen_discrete _⟩

lemma pointOpen_basis : Opens.IsBasis (Set.range (pointOpen (X := X))) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U x hx
  exact ⟨pointOpen x, ⟨x,rfl⟩, rfl, fun y hy => by cases hy; exact hx⟩

def pointFrame (L : LineBundle X) (x : X) :
    L.sheaf.val.obj (op (pointOpen x)) ≅
      (structureSheaf X).val.obj (op (pointOpen x)) := by
  let U := (L.locallyRankOne x).choose
  have hx := (L.locallyRankOne x).choose_spec.1
  let e := (L.locallyRankOne x).choose_spec.2.some
  let h : pointOpen x ≤ U := fun y hy => by cases hy; exact hx
  let e' := overFrame e
  exact (SheafOfModules.evaluation (X.ringCatSheaf.over U) (op (Over.mk (homOfLE h)))).mapIso e'

theorem lineBundle_trivial (L : LineBundle X) : Nonempty (L.sheaf ≅ structureSheaf X) := by
  classical
  let F : TopCat.Sheaf AddCommGrpCat.{0} X.toTopCat :=
    (SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj L.sheaf
  let B := pointOpen (X := X)
  let t : ∀ x, Γ(L.sheaf,B x) := fun x => (pointFrame L x).inv (1 : Γ(X,B x))
  have hc : TopCat.Presheaf.IsCompatible F.obj B t := by
    intro x y
    by_cases h : x = y
    · subst y; rfl
    · have he : B x ⊓ B y = ⊥ := by
        ext z
        change (z = x ∧ z = y) ↔ False
        constructor
        · rintro ⟨rfl,h'⟩; exact h h'
        · tauto
      let : Subsingleton (F.obj.obj (op (B x ⊓ B y))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty he).isZero
      exact Subsingleton.elim _ _
  have hcover : (⊤ : X.Opens) ≤ ⨆ x, B x := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x,rfl⟩
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' B ⊤ (fun _ => homOfLE le_top) hcover t hc
  let s : structureSheaf X ⟶ L.sheaf :=
    (FlasqueCohomology.globalHomEquiv X.ringCatSheaf L.sheaf).symm a
  have hs (x : X) : s.val.app (op (B x)) = (pointFrame L x).inv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X,B x) at r
    have hs1 : s.val.app (op (B x)) (1 : Γ(X,B x)) = t x := by
      have htop : s.app ⊤ (1 : Γ(X,⊤)) = a :=
        (FlasqueCohomology.globalHomEquiv X.ringCatSheaf L.sheaf).apply_symm_apply a
      have hn := CategoryTheory.congr_fun (s.mapPresheaf.naturality
        (homOfLE (show B x ≤ ⊤ from le_top)).op) (1 : Γ(X,⊤))
      change s.app (B x) (X.presheaf.map (homOfLE le_top).op 1) =
        L.sheaf.presheaf.map (homOfLE le_top).op (s.app ⊤ (1 : Γ(X,⊤))) at hn
      have hax : L.sheaf.presheaf.map (homOfLE (show B x ≤ ⊤ from le_top)).op a = t x := ha x
      have hn' : s.app (B x) (1 : Γ(X,B x)) =
          L.sheaf.presheaf.map (homOfLE le_top).op a := by
        simpa only [map_one, htop] using hn
      exact hn'.trans hax
    let : Module Γ(X,B x) (L.sheaf.val.obj (op (B x))) :=
      (L.sheaf.val.obj (op (B x))).isModule
    calc
      s.val.app (op (B x)) r = r • s.val.app (op (B x)) (1 : Γ(X,B x)) := by
        exact (congrArg (s.val.app (op (B x))) (mul_one r).symm).trans
          ((s.val.app (op (B x))).hom.map_smul r (1 : Γ(X,B x)))
      _ = r • (pointFrame L x).inv (1 : Γ(X,B x)) := by rw [hs1]
      _ = (pointFrame L x).inv r := by
        exact ((pointFrame L x).inv.hom.map_smul r (1 : Γ(X,B x))).symm.trans
          (congrArg (pointFrame L x).inv (mul_one r))
  have hiso : IsIso ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).map s) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis pointOpen_basis
    intro x
    change IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map (s.val.app (op (B x))))
    rw [hs]
    infer_instance
  let : Mono s := (SheafOfModules.toSheaf.{0} X.ringCatSheaf).mono_of_mono_map inferInstance
  let : Epi s := (SheafOfModules.toSheaf.{0} X.ringCatSheaf).epi_of_epi_map inferInstance
  let : IsIso s := isIso_of_mono_of_epi s
  exact ⟨(asIso s).symm⟩

end

open CategoryTheory AlgebraicGeometry PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem finite_line_pushforward_euler (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X]
    (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic g d ((Scheme.Modules.pushforward f).obj L.sheaf) =
      let _ : Algebra ℂ Γ(X,⊤) := (baseScalars (f ≫ g)).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  let : DiscreteTopology X := proper_finite_discrete (f ≫ g)
  obtain ⟨e⟩ := lineBundle_trivial L
  rw [eulerCharacteristic_iso g ((Scheme.Modules.pushforward f).mapIso e) d]
  exact finite_pushforward_euler f g d

theorem finite_line_pushforward_finiteDimensional (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X]
    (L : LineBundle X) (n : ℕ) :
    let M := (Scheme.Modules.pushforward f).obj L.sheaf
    let _ := Module.compHom (cohomology M n) (baseScalars g)
    FiniteDimensional ℂ (cohomology M n) := by
  let : DiscreteTopology X := proper_finite_discrete (f ≫ g)
  obtain ⟨e⟩ := lineBundle_trivial L
  let M := (Scheme.Modules.pushforward f).obj L.sheaf
  let N := (Scheme.Modules.pushforward f).obj (structureSheaf X)
  let := Module.compHom (cohomology M n) (baseScalars g)
  let := Module.compHom (cohomology N n) (baseScalars g)
  let : FiniteDimensional ℂ (cohomology N n) := finite_pushforward_finiteDimensional f g n
  exact Module.Finite.of_surjective
    (cohomologyIso g ((Scheme.Modules.pushforward f).mapIso e) n).symm.toLinearMap
    (cohomologyIso g ((Scheme.Modules.pushforward f).mapIso e) n).symm.surjective

theorem finite_line_euler_eq_sum_stalks (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Fintype X]
    (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic g d ((Scheme.Modules.pushforward f).obj L.sheaf) =
      ∑ x : X, let _ := structuralStalkAlgebra (f ≫ g) x
        (Module.finrank ℂ (X.presheaf.stalk x) : ℤ) := by
  rw [finite_line_pushforward_euler]
  dsimp only
  have h := proper_finite_finrank_eq_sum_stalks (f ≫ g)
  dsimp only at h
  exact_mod_cast h

theorem finite_line_euler_eq_sum_stalk_lengths (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Fintype X]
    (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic g d ((Scheme.Modules.pushforward f).obj L.sheaf) =
      ∑ x : X, ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) := by
  calc
    _ = eulerCharacteristic (f ≫ g) d (structureSheaf X) :=
      (finite_line_pushforward_euler f g L d).trans (proper_finite_euler (f ≫ g) d).symm
    _ = _ := proper_finite_euler_eq_sum_stalk_lengths (f ≫ g) d

end PiExponentSeshadri.FiniteSupport

end

end OAI

import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.LineBundleCoherent
import OAI.AlgebraicGeometry.Seshadri.Cohomology.AffineVanishing

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.FiniteSupport
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open MaximalSeshadri.Geometry

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
    apply LinearMap.ext_ring
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
    exact hs1
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
end MaximalSeshadri.FiniteSupport
end


end
end

end OAI

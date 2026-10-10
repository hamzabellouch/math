import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.SectionOpens
import OAI.AlgebraicGeometry.Seshadri.Sheaves.Sections

namespace OAI

section
noncomputable section
noncomputable section
open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.finite_cover_power_extension [IsIntegral X] (L : LineBundle X)
    {ι : Type*} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ i, IsAffine (U i).toScheme)
    (hU : ∀ i, (U i : Set X).Nonempty)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ structureSheaf (U i).toScheme)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ(X, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      t.app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) =
        f • (powerSection s n).app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) := by
  classical
  let D := sectionOpen X s
  let V (i : ι) := (U i).toScheme.basicOpen (coefficient (e i) (restrictSection (U i).ι s))
  let W (i : ι) := (U i).ι ''ᵁ V i
  have hV (i : ι) : V i = (U i).ι ⁻¹ᵁ D :=
    (preimage_isoOpen s (U i).ι (e i)).symm
  have hW_eq (i : ι) : W i = U i ⊓ D := by
    simp only [W, hV, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hWU (i : ι) : W i ≤ U i := (U i).ι_image_le (V i)
  have hWD (i : ι) : W i ≤ D := (hW_eq i).le.trans inf_le_right
  have hW (i : ι) : (W i : Set X).Nonempty := by
    rw [hW_eq]
    exact nonempty_preirreducible_inter (U i).isOpen D.isOpen (hU i) hD
  let fi (i : ι) : Γ((V i).toScheme, ⊤) :=
    (V i).topIso.inv (((U i).ι.appIso (V i)).hom (X.presheaf.map (homOfLE (hWD i)).op f))
  have hf (i : ι) : ∃ N : ℕ, ∀ n ≥ N,
      ∃ t : structureSheaf (U i).toScheme ⟶ (modulePow X L.sheaf n).restrict (U i).ι,
        restrictSection (V i).ι t = scalarEnd (fi i) ≫
          restrictSection (V i).ι (restrictSection (U i).ι (powerSection s n)) := by
    let := haff i
    exact local_affine_power_extension (U i) (e i) s (fi i)
  choose N hN using hf
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  have hn' (i : ι) : N i ≤ n := (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  choose t ht using fun i => hN i n (hn' i)
  let M := modulePow X L.sheaf n
  let target : Γ((L.pow n).sheaf, D) := f • (powerSection s n).app D (1 : Γ(X, D))
  have heq (i : ι) : M.presheaf.map (homOfLE (hWU i)).op (openSectionEquiv M (U i) (t i)) =
      M.presheaf.map (homOfLE (hWD i)).op target := by
    have hi := image_section_extension M (U i) (restrictSection (U i).ι (powerSection s n))
      (t i) (V i) (fi i) (ht i)
    have hfi : ((U i).ι.appIso (V i)).inv ((V i).topIso.hom (fi i)) =
        X.presheaf.map (homOfLE (hWD i)).op f := by
      dsimp only [fi]
      rw [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply]
    rw [hfi] at hi
    have hp : openSectionEquiv M (U i) (restrictSection (U i).ι (powerSection s n)) =
        (powerSection s n).app (U i) (1 : Γ(X, U i)) := openSectionEquiv_restrict _ _
    have hs : M.presheaf.map (homOfLE (hWU i)).op
        (openSectionEquiv M (U i) (restrictSection (U i).ι (powerSection s n))) =
        (powerSection s n).app (W i) (1 : Γ(X, W i)) :=
      (congrArg (M.presheaf.map (homOfLE (hWU i)).op) hp).trans
        (section_value_natural (powerSection s n) (homOfLE (hWU i)))
    have hr : M.presheaf.map (homOfLE (hWD i)).op target =
        X.presheaf.map (homOfLE (hWD i)).op f •
          (powerSection s n).app (W i) (1 : Γ(X, W i)) :=
      (M.map_smul (homOfLE (hWD i)) f _).trans
        (congrArg (X.presheaf.map (homOfLE (hWD i)).op f • ·)
          (section_value_natural (powerSection s n) (homOfLE (hWD i))))
    exact (hi.trans (congrArg (X.presheaf.map (homOfLE (hWD i)).op f • ·) hs)).trans hr.symm
  obtain ⟨g, hg, -⟩ := (L.pow n).glue_dense_subopens D U W hcover hWU hWD hW
    (fun i => openSectionEquiv M (U i) (t i)) target heq
  refine ⟨(moduleSectionEquiv M).symm g, ?_⟩
  have H := section_value_natural ((moduleSectionEquiv M).symm g)
    (homOfLE (show D ≤ ⊤ from le_top))
  have Htop : ((moduleSectionEquiv M).symm g).app ⊤ (1 : Γ(X, ⊤)) = g :=
    (moduleSectionEquiv M).apply_symm_apply g
  rw [Htop] at H
  exact H.symm.trans hg.2

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.InvertibleLocal
noncomputable section
open CategoryTheory AlgebraicGeometry
open MaximalSeshadri.Geometry
variable {X Y : Scheme}

def frameOfLE (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.restrict V.ι ≅ structureSheaf V.toScheme := by
  let e' := (Scheme.Modules.restrictFunctorComp (Y.homOfLE h) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (Y.homOfLE h)
  simp only [Y.homOfLE_ι h] at e'
  exact e'

lemma affine_frame (J : LineBundle Y) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧
      Nonempty (J.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
  obtain ⟨V, hyV, ⟨e⟩⟩ := J.locallyRankOne y
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset hyV
  exact ⟨⟨U, hU⟩, hyU, ⟨frameOfLE J.sheaf hUV e⟩⟩

end
end MaximalSeshadri.InvertibleLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open MaximalSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.power_extension [IsIntegral X] [CompactSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ(X, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      t.app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) =
        f • (powerSection s n).app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) := by
  classical
  choose U hUx he using InvertibleLocal.affine_frame L
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x).1 : X → Set X) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hUx x⟩)
  have hic (x : X) : ∃ i ∈ I, x ∈ (U i).1 := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hi, hx⟩
  have : Nonempty I := by
    obtain ⟨x, -⟩ := hD
    obtain ⟨i, hi, -⟩ := hic x
    exact ⟨⟨i, hi⟩⟩
  exact L.finite_cover_power_extension (fun i : I => (U i.val).1)
    (by
      intro x _
      obtain ⟨i, hi, hx⟩ := hic x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩)
    (fun i => (U i.val).2) (fun i => ⟨i.val, hUx i.val⟩)
    (fun i => Classical.choice (he i.val)) s hD f

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.TensorLocalization
noncomputable section
open CategoryTheory MonoidalCategory
universe v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

lemma map_tensor_right_unit {P Q L : C} (f : P ⟶ Q) (e : L ≅ 𝟙_ C)
    [IsIso (F.map f)] : IsIso (F.map (f ⊗ₘ 𝟙 L)) := by
  let ε (A : C) : A ⊗ L ≅ A := tensorIso (Iso.refl A) e ≪≫ ρ_ A
  have h : (f ⊗ₘ 𝟙 L) ≫ (ε Q).hom = (ε P).hom ≫ f := by
    simp only [ε, Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    have ht : f ⊗ₘ e.hom = (𝟙 P ⊗ₘ e.hom) ≫ (f ⊗ₘ 𝟙 (𝟙_ C)) := by
      rw [tensorHom_comp_tensorHom]
      simp only [Category.id_comp, Category.comp_id]
    rw [ht, Category.assoc, tensorHom_id, rightUnitor_naturality, Category.assoc]
  have hh : IsIso (F.map ((f ⊗ₘ 𝟙 L) ≫ (ε Q).hom)) := by
    rw [h, F.map_comp]
    infer_instance
  rw [F.map_comp] at hh
  exact (isIso_comp_right_iff _ _).mp hh

end
end MaximalSeshadri.TensorLocalization

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma sheafification_tensor_right_isIso
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ Q) (L : LineBundle X)
    [IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f (𝟙 L.sheaf.val))) := by
  let sheafificationIso := asIso
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)
  apply SectionOpens.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let R := modulePresheafRestrict U.ι
  let S := PresheafOfModules.sheafification (R := U.toScheme.ringCatSheaf)
    (𝟙 U.toScheme.ringCatSheaf.obj)
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  have hf : IsIso (S.map (R.map f)) := by
    apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) f).mp
    change IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f))
    exact ((Scheme.Modules.restrictFunctor U.ι).mapIso sheafificationIso).isIso_hom
  let ep : R.obj L.sheaf.val ≅ 𝟙_ (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    (SheafOfModules.forget _).mapIso e
  have ht : IsIso (S.map ((R.map f) ⊗ₘ 𝟙 (R.obj L.sheaf.val))) :=
    TensorLocalization.map_tensor_right_unit S (R.map f) ep
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) _).mpr
  let g := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f (𝟙 L.sheaf.val)
  change IsIso (S.map (R.map g))
  have heq := modulePresheafTensorRestrict_natural U f (𝟙 L.sheaf.val)
  have hcomp : IsIso (S.map (R.map g ≫
      (modulePresheafTensorRestrict U Q L.sheaf.val).hom)) := by
    rw [heq]
    erw [S.map_comp]
    have ht' : IsIso (S.map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map f) (R.map (𝟙 L.sheaf.val)))) := by
      erw [R.map_id]
      exact ht
    exact IsIso.comp_isIso'
      (S.mapIso (modulePresheafTensorRestrict U P L.sheaf.val)).isIso_hom ht'
  erw [S.map_comp] at hcomp
  have : IsIso (S.map (modulePresheafTensorRestrict U Q L.sheaf.val).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U Q L.sheaf.val)).isIso_hom
  exact (isIso_comp_right_iff _ _).mp hcomp

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory BraidedCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma sheafification_tensor_left_isIso
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ Q) (L : LineBundle X)
    [IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) (𝟙 L.sheaf.val) f)) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have := sheafification_tensor_right_isIso f L
  have h : IsIso (F.map ((𝟙 L.sheaf.val ⊗ₘ f) ≫ (β_ L.sheaf.val Q).hom)) := by
    rw [braiding_naturality, F.map_comp]
    infer_instance
  rw [F.map_comp] at h
  exact (isIso_comp_right_iff _ _).mp h

def sheafificationTensorRight (P : PresheafOfModules X.ringCatSheaf.obj)
    (L : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) P L.sheaf.val) ≅
    moduleTensor X ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P)
      L.sheaf := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have : IsIso (F.map η) :=
    isIso_of_comp_hom_eq_id _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P)
  have ht : IsIso (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      η (𝟙 L.sheaf.val))) := sheafification_tensor_right_isIso η L
  exact @asIso _ _ _ _ (F.map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      η (𝟙 L.sheaf.val))) ht

def sheafificationTensorLeft (P : PresheafOfModules X.ringCatSheaf.obj)
    (L : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val P) ≅
    moduleTensor X L.sheaf
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have : IsIso (F.map η) :=
    isIso_of_comp_hom_eq_id _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P)
  have ht : IsIso (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      (𝟙 L.sheaf.val) η)) := sheafification_tensor_left_isIso η L
  exact @asIso _ _ _ _ (F.map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
      (𝟙 L.sheaf.val) η)) ht

def lineTensorAssoc (L M N : LineBundle X) :
    moduleTensor X (moduleTensor X L.sheaf M.sheaf) N.sheaf ≅
      moduleTensor X L.sheaf (moduleTensor X M.sheaf N.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (sheafificationTensorRight (L.sheaf.val ⊗ M.sheaf.val) N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (α_ L.sheaf.val M.sheaf.val N.sheaf.val) ≪≫
    sheafificationTensorLeft (M.sheaf.val ⊗ N.sheaf.val) L

def moduleTensorRightUnit (M : X.Modules) :
    moduleTensor X M (structureSheaf X) ≅ M := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (ρ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).counit).app M

def linePowerAdd (L : LineBundle X) : ∀ m n : ℕ,
    modulePow X L.sheaf (m + n) ≅
      moduleTensor X (modulePow X L.sheaf m) (modulePow X L.sheaf n)
  | 0, n => by
      simpa only [Nat.zero_add, modulePow, structureSheaf] using (moduleTensorUnit (modulePow X L.sheaf n)).symm
  | m + 1, n => by
      rw [Nat.succ_add]
      exact moduleTensorIso (Iso.refl _) (linePowerAdd L m n) ≪≫
        (lineTensorAssoc L (L.pow m) (L.pow n)).symm

def linePowerMul (L : LineBundle X) (m : ℕ) : ∀ n : ℕ,
    modulePow X (modulePow X L.sheaf m) n ≅ modulePow X L.sheaf (m * n)
  | 0 => Iso.refl _
  | n + 1 => by
      rw [Nat.mul_succ, Nat.add_comm (m * n) m]
      exact moduleTensorIso (Iso.refl _) (linePowerMul L m n) ≪≫
        (linePowerAdd L m (m * n)).symm

end
end MaximalSeshadri.Geometry

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.common_degree (L : LineBundle X) {ι : Type} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (s : ∀ i, GlobalSections X (modulePow X L.sheaf (d i))) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : ι → GlobalSections X (modulePow X L.sheaf n),
      ∀ i, sectionOpen X (t i) = sectionOpen X (s i) := by
  classical
  let n := ∏ i, d i
  have hn : 0 < n := Finset.prod_pos (fun i _ => hd i)
  have hdiv (i : ι) : d i ∣ n := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have heq (i : ι) : d i * (n / d i) = n := Nat.mul_div_cancel' (hdiv i)
  let e (i : ι) : modulePow X (modulePow X L.sheaf (d i)) (n / d i) ≅
      modulePow X L.sheaf n :=
    linePowerMul L (d i) (n / d i) ≪≫ eqToIso (congrArg (modulePow X L.sheaf) (heq i))
  refine ⟨n, hn, fun i => powerSection (s i) (n / d i) ≫ (e i).hom, ?_⟩
  intro i
  change SectionOpens.isoOpen (powerSection (s i) (n / d i) ≫ (e i).hom) = _
  rw [SectionOpens.isoOpen_postcomp]
  exact (L.pow (d i)).sectionOpen_power (s i)
    (Nat.div_pos (Nat.le_of_dvd hn (hdiv i)) (hd i))

theorem LineBundle.ample_common_degree_cover [CompactSpace X] (L : LineBundle X)
    (hL : LineBundle.IsAmple X L) :
    ∃ n : ℕ, 0 < n ∧ ∃ l : ℕ,
      ∃ s : Fin l → GlobalSections X (modulePow X L.sheaf n),
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) := by
  classical
  have hex (x : X) := hL x ⊤ (by trivial)
  choose d hd s hs hst ha using hex
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hs x⟩)
  obtain ⟨n, hn, t, ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let e := (Fintype.equivFin I).symm
  refine ⟨n, hn, Fintype.card I, fun i => t (e i), ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨e.symm ⟨i, hi⟩, ?_⟩
    change x ∈ sectionOpen X (t (e (e.symm ⟨i, hi⟩)))
    rw [Equiv.apply_symm_apply, ht]
    exact hx
  · intro i
    rw [ht]
    exact ha (e i).val
  · intro i
    rw [ht]
    exact ⟨(e i).val, hs (e i).val⟩

end
end MaximalSeshadri.Geometry


end
end
end

end OAI

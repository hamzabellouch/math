import OAI.NumberTheory.PiExponent.Approximation.FrameSections
import OAI.NumberTheory.PiExponent.Approximation.IntegralLineSections
import OAI.NumberTheory.PiExponent.Approximation.SectionPowerOpens

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Frames
open CategoryTheory AlgebraicGeometry
@[simp] lemma coefficient_scalarEnd {X : Scheme} {M : X.Modules}
    (e : M ≅ O X) (a : Γ(X, ⊤)) :
    coefficient e (scalarEnd a ≫ e.inv) = a := by
  simp only [coefficient, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    endValue_scalarEnd]
end Frames

namespace Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

lemma affine_function_denom [IsAffine X] (a : Γ(X, ⊤))
    (f : Γ((X.basicOpen a).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ g : Γ(X, ⊤),
      (X.basicOpen a).ι.appTop g = f * (X.basicOpen a).ι.appTop a ^ n := by
  obtain ⟨N, g, hg⟩ := IsLocalization.Away.surj a f
  refine ⟨N, fun n hn => ⟨g * a ^ (n - N), ?_⟩⟩
  change algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) (g * a ^ (n - N)) =
    f * algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) a ^ n
  rw [map_mul, map_pow, ← hg, mul_assoc, ← pow_add, Nat.add_sub_of_le hn]

theorem local_affine_power_extension (U : X.Opens) [IsAffine U.toScheme]
    {M : X.Modules} (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (s : GlobalSections X M)
    (f : Γ((U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : structureSheaf U.toScheme ⟶ (modulePow X M n).restrict U.ι,
      restrictSection (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).ι t =
        scalarEnd f ≫ restrictSection
          (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).ι
          (restrictSection U.ι (powerSection s n)) := by
  let a := coefficient e (restrictSection U.ι s)
  obtain ⟨N, hN⟩ := affine_function_denom a f
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨g, hg⟩ := hN n hn
  let eₙ := localPowerFrame U e n
  let c := endValue (powerRestrictionUnit U n).hom
  let φ := (U.toScheme.basicOpen a).ι
  refine ⟨scalarEnd (c * g) ≫ eₙ.inv, ?_⟩
  apply coefficient_injective (restrictFrame φ eₙ)
  calc
    _ = φ.appTop (c * g) := (coefficient_restrict φ eₙ _).trans
      (congrArg φ.appTop (coefficient_scalarEnd eₙ (c * g)))
    _ = φ.appTop c * φ.appTop g := map_mul φ.appTop.hom c g
    _ = φ.appTop c * (f * φ.appTop a ^ n) := congrArg (φ.appTop c * ·) hg
    _ = f * φ.appTop (c * a ^ n) := by
      simp only [map_mul, map_pow]
      ring
    _ = f * φ.appTop (coefficient eₙ (restrictSection U.ι (powerSection s n))) :=
      congrArg (fun z => f * φ.appTop z) (local_powerSection_coefficient U e s n).symm
    _ = endValue (scalarEnd f) * coefficient (restrictFrame φ eₙ)
        (restrictSection φ (restrictSection U.ι (powerSection s n))) :=
      congrArg₂ (· * ·) (endValue_scalarEnd f).symm (coefficient_restrict φ eₙ _).symm
    _ = _ := (coefficient_precompose _ _ _).symm

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.glue_dense_subopens [IsIntegral X] (L : LineBundle X)
    (D : X.Opens) {ι : Type*} [Nonempty ι] (U W : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (hWU : ∀ i, W i ≤ U i) (hWD : ∀ i, W i ≤ D)
    (hW : ∀ i, (W i : Set X).Nonempty)
    (sf : ∀ i, Γ(L.sheaf, U i)) (target : Γ(L.sheaf, D))
    (heq : ∀ i, L.sheaf.presheaf.map (homOfLE (hWU i)).op (sf i) =
      L.sheaf.presheaf.map (homOfLE (hWD i)).op target) :
    ∃! g : Γ(L.sheaf, ⊤),
      (∀ i, L.sheaf.presheaf.map (homOfLE le_top).op g = sf i) ∧
        L.sheaf.presheaf.map (homOfLE le_top).op g = target := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨L.sheaf.presheaf, L.sheaf.isSheaf⟩
  have hc : TopCat.Presheaf.IsCompatible L.sheaf.presheaf U sf := by
    intro i j
    have : Nonempty (W i ⊓ W j : X.Opens) := by
      obtain ⟨x, hi, hj⟩ := nonempty_preirreducible_inter (W i).isOpen (W j).isOpen
        (hW i) (hW j)
      exact ⟨⟨x, hi, hj⟩⟩
    apply L.restriction_injective (homOfLE
      (show W i ⊓ W j ≤ U i ⊓ U j from fun _ hx => ⟨hWU i hx.1, hWU j hx.2⟩))
    have hi := congrArg (L.sheaf.presheaf.map (infLELeft (W i) (W j)).op) (heq i)
    have hj := congrArg (L.sheaf.presheaf.map (infLERight (W i) (W j)).op) (heq j)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hi hj ⊢
    exact hi.trans hj.symm
  obtain ⟨g, hg, hguniq⟩ := F.existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) hcover sf hc
  have hD : L.sheaf.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op g = target := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have : Nonempty (W i) := by obtain ⟨x, hx⟩ := hW i; exact ⟨⟨x, hx⟩⟩
    apply L.restriction_injective (homOfLE (hWD i))
    have hi : L.sheaf.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op g = sf i := hg i
    have hgi := congrArg (L.sheaf.presheaf.map (homOfLE (hWU i)).op) hi
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hgi ⊢
    exact hgi.trans (heq i)
  exact ⟨g, ⟨hg, hD⟩, fun g' h' => hguniq g' h'.1⟩

end

open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
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

end Geometry

namespace InvertibleLocal
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
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

end InvertibleLocal

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
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

end Geometry

end PiExponentSeshadri

end

end OAI

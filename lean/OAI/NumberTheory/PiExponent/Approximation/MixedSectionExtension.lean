import OAI.NumberTheory.PiExponent.Approximation.PowerSectionExtension
import OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

theorem local_affine_mixed_extension (L M : LineBundle X) (U : X.Opens) [IsAffine U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (s : O X ⟶ L.sheaf)
    (w : Γ(M.sheaf, U.ι ''ᵁ (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))))) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O U.toScheme ⟶ (((L.pow n).tensor M).sheaf.restrict U.ι),
      let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
      (((L.pow n).tensor M).sheaf).presheaf.map (homOfLE (U.ι_image_le V)).op
        (openSectionEquiv _ U t) =
      pure (L.pow n).sheaf M.sheaf (U.ι ''ᵁ V) ((powerSection s n).app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V))) w := by
  let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let b : Γ(U.toScheme,V) := d.hom.app V w
  let f : Γ(V.toScheme,⊤) := V.topIso.inv b
  obtain ⟨N,hN⟩ := local_affine_power_extension U e s f
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht⟩ := hN n hn
  let q : O U.toScheme ⟶ (((L.pow n).tensor M).sheaf.restrict U.ι) :=
    TensorPure.tensorSection t d.inv ≫ (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv
  refine ⟨q,?_⟩
  change (((L.pow n).tensor M).sheaf).presheaf.map (homOfLE (U.ι_image_le V)).op
    (openSectionEquiv _ U q) = _
  erw [openSectionEquiv_restrict_value ((L.pow n).tensor M).sheaf U q V]
  have he := congrArg (openSectionEquiv ((L.pow n).sheaf.restrict U.ι) V) ht
  erw [openSectionEquiv_restrict t V,
    openSectionEquiv_scalar ((L.pow n).sheaf.restrict U.ι) V f
      (restrictSection V.ι (restrictSection U.ι (powerSection s n))),
    openSectionEquiv_restrict (restrictSection U.ι (powerSection s n)) V] at he
  have hf : V.topIso.hom f = b := Iso.inv_hom_id_apply _ _
  rw [hf] at he
  have hp : (restrictSection U.ι (powerSection s n)).app V (1 : Γ(U.toScheme,V)) =
      (powerSection s n).app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V)) := by
    change (powerSection s n).app (U.ι ''ᵁ V) ((U.ι.appIso V).inv (1 : Γ(U.toScheme,V))) = _
    rw [map_one]
  have he := he.trans (congrArg (fun z : Γ((L.pow n).sheaf.restrict U.ι, V) => (b : Γ(U.toScheme,V)) • z) hp)
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf U.toScheme).mapIso
      (moduleTensorRestrict U (L.pow n).sheaf M.sheaf)).app (op V)).hom).injective
  change (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom.app V
      ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv.app V
        ((TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)))) = _
  have hc : (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom.app V
      ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv.app V
        ((TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)))) = (TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)) := by
    change ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv ≫
      (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom).app V _ = _
    rw [Iso.inv_hom_id]
    rfl
  erw [hc,TensorPure.section_apply t d.inv V]
  refine (congrArg (fun z => pure ((L.pow n).sheaf.restrict U.ι) (M.sheaf.restrict U.ι) V
    z (d.inv.app V (1 : Γ(U.toScheme,V)))) he).trans ?_
  erw [pure_smul_left,← pure_smul_right]
  have hd : b • d.inv.app V (1 : Γ(U.toScheme,V)) = w := by
    erw [← d.inv.app_smul b (1 : Γ(U.toScheme,V)),smul_eq_mul,mul_one]
    change d.inv.app V (d.hom.app V w) = w
    change (d.hom ≫ d.inv).app V w = w
    rw [Iso.hom_inv_id]
    rfl
  erw [hd]
  exact (restrict_pure U (L.pow n).sheaf M.sheaf V _ w).symm

theorem LineBundle.finite_cover_mixed_extension [IsIntegral X] (L M : LineBundle X)
    {ι : Type*} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ i, IsAffine (U i).toScheme) (hU : ∀ i, (U i : Set X).Nonempty)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ O (U i).toScheme)
    (d : ∀ i, M.sheaf.restrict (U i).ι ≅ O (U i).toScheme)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow n).tensor M).sheaf,
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow n).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s n).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  classical
  let D := sectionOpen X s
  let V (i : ι) := (U i).toScheme.basicOpen (coefficient (e i) (restrictSection (U i).ι s))
  let W (i : ι) := (U i).ι ''ᵁ V i
  have hV (i : ι) : V i = (U i).ι ⁻¹ᵁ D := (preimage_isoOpen s (U i).ι (e i)).symm
  have hW_eq (i : ι) : W i = U i ⊓ D := by
    simp only [W,hV,Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι]
  have hWU (i : ι) : W i ≤ U i := (U i).ι_image_le (V i)
  have hWD (i : ι) : W i ≤ D := (hW_eq i).le.trans inf_le_right
  have hW (i : ι) : (W i : Set X).Nonempty := by
    rw [hW_eq]
    exact nonempty_preirreducible_inter (U i).isOpen D.isOpen (hU i) hD
  let wi (i : ι) : Γ(M.sheaf,W i) := M.sheaf.presheaf.map (homOfLE (hWD i)).op w
  have hh (i : ι) := @local_affine_mixed_extension X L M (U i) (haff i) (e i) (d i) s (wi i)
  choose N hN using hh
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  have hn' (i : ι) : N i ≤ n := (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  choose t ht using fun i => hN i n (hn' i)
  let P := ((L.pow n).tensor M)
  let target : Γ(P.sheaf,D) := pure (L.pow n).sheaf M.sheaf D
    ((powerSection s n).app D (1 : Γ(X,D))) w
  have heq (i : ι) : P.sheaf.presheaf.map (homOfLE (hWU i)).op
      (openSectionEquiv P.sheaf (U i) (t i)) =
      P.sheaf.presheaf.map (homOfLE (hWD i)).op target := by
    refine (ht i).trans ?_
    have hr := pure_restrict (L.pow n).sheaf M.sheaf (homOfLE (hWD i))
      ((powerSection s n).app D (1 : Γ(X,D))) w
    have hp := section_value_natural (powerSection s n) (homOfLE (hWD i))
    exact (congrArg (fun z => pure (L.pow n).sheaf M.sheaf (W i) z (wi i)) hp).symm.trans hr.symm
  obtain ⟨g,hg,-⟩ := P.glue_dense_subopens D U W hcover hWU hWD hW
    (fun i => openSectionEquiv P.sheaf (U i) (t i)) target heq
  refine ⟨(moduleSectionEquiv P.sheaf).symm g,?_⟩
  have H := section_value_natural ((moduleSectionEquiv P.sheaf).symm g)
    (homOfLE (show D ≤ ⊤ from le_top))
  have Htop : ((moduleSectionEquiv P.sheaf).symm g).app ⊤ (1 : Γ(X,⊤)) = g :=
    (moduleSectionEquiv P.sheaf).apply_symm_apply g
  rw [Htop] at H
  exact H.symm.trans hg.2

theorem LineBundle.mixed_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow n).tensor M).sheaf,
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow n).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s n).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  classical
  choose U hUx he hd using common_affine_frames L M
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x).1 : X → Set X) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hUx x⟩)
  have hic (x : X) : ∃ i ∈ I, x ∈ (U i).1 := by
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨i,hi,hx⟩
  have : Nonempty I := by
    obtain ⟨x,-⟩ := hD
    obtain ⟨i,hi,-⟩ := hic x
    exact ⟨⟨i,hi⟩⟩
  exact L.finite_cover_mixed_extension M (fun i : I => (U i.val).1)
    (by intro x _; obtain ⟨i,hi,hx⟩ := hic x; exact Opens.mem_iSup.mpr ⟨⟨i,hi⟩,hx⟩)
    (fun i => (U i.val).2) (fun i => ⟨i.val,hUx i.val⟩)
    (fun i => Classical.choice (he i.val)) (fun i => Classical.choice (hd i.val)) s hD w

end PiExponentSeshadri.Geometry

end

end OAI

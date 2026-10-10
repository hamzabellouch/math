import Mathlib

namespace OAI

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveStalkGluing

universe u

variable {X Y S : Scheme.{u}} [IsIntegral X]

@[reassoc]
theorem specMap_stalkFunctionField_fromSpecStalk (x : X) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ X.fromSpecStalk x =
      X.fromSpecStalk (genericPoint X) := by
  change Spec.map (X.presheaf.stalkSpecializes
    ((genericPoint_spec X).specializes trivial)) ≫ X.fromSpecStalk x = _
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _

theorem isDominant_fromSpecFunctionField :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure X]
  apply closure_mono
  rw [Set.singleton_subset_iff]
  exact ⟨IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)), by simp⟩

theorem genericPoint_mem (U : X.Opens) (x : X) (hx : x ∈ U) :
    genericPoint X ∈ U :=
  (genericPoint_specializes x).mem_open U.isOpen hx

@[reassoc]
theorem specMap_stalkFunctionField_fromSpecStalkOfMem
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        U.fromSpecStalkOfMem x hx =
      U.fromSpecStalkOfMem (genericPoint X) (genericPoint_mem U x hx) := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    specMap_stalkFunctionField_fromSpecStalk]


theorem overlap_eq (sX : X ⟶ S) (sY : Y ⟶ S) [IsSeparated sY]
    (η : Spec X.functionField ⟶ Y) (U V : X.Opens)
    (hU : genericPoint X ∈ U) (hV : genericPoint X ∈ V)
    (f : U.toScheme ⟶ Y) (g : V.toScheme ⟶ Y)
    (hf : f ≫ sY = U.ι ≫ sX) (hg : g ≫ sY = V.ι ≫ sX)
    (hfη : U.fromSpecStalkOfMem (genericPoint X) hU ≫ f = η)
    (hgη : V.fromSpecStalkOfMem (genericPoint X) hV ≫ g = η) :
    pullback.fst U.ι V.ι ≫ f = pullback.snd U.ι V.ι ≫ g := by
  let a := U.fromSpecStalkOfMem (genericPoint X) hU
  let b := V.fromSpecStalkOfMem (genericPoint X) hV
  have hab : a ≫ U.ι = b ≫ V.ι := by simp [a, b]
  let k : Spec X.functionField ⟶ pullback U.ι V.ι := pullback.lift a b hab
  let q : pullback U.ι V.ι ⟶ X := pullback.fst U.ι V.ι ≫ U.ι
  have hkq : k ≫ q = X.fromSpecStalk (genericPoint X) := by
    dsimp only [k, q]
    rw [← Category.assoc, pullback.lift_fst]
    exact Scheme.Opens.fromSpecStalkOfMem_ι U _ hU
  have : IsReduced (pullback U.ι V.ι) := isReduced_of_isOpenImmersion q
  have : IsDominant (k ≫ q) := by
    rw [hkq]
    exact isDominant_fromSpecFunctionField
  have : IsDominant k := IsDominant.of_comp_of_isOpenImmersion k q
  have hover : (pullback.fst U.ι V.ι ≫ f) ≫ sY =
      (pullback.snd U.ι V.ι ≫ g) ≫ sY := by
    rw [Category.assoc, hf, Category.assoc, hg]
    exact pullback.condition_assoc (f := U.ι) (g := V.ι) sX
  have hgeneric : k ≫ (pullback.fst U.ι V.ι ≫ f) =
      k ≫ (pullback.snd U.ι V.ι ≫ g) := by
    dsimp only [k]
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    exact hfη.trans hgη.symm
  exact ext_of_isDominant_of_isSeparated sY hover k hgeneric


theorem exists_morphism_of_stalk_maps
    (sX : X ⟶ S) (sY : Y ⟶ S) [LocallyOfFiniteType sY] [IsSeparated sY]
    (η : Spec X.functionField ⟶ Y)
    (H : ∀ x : X, ∃ φ : Spec (X.presheaf.stalk x) ⟶ Y,
      φ ≫ sY = X.fromSpecStalk x ≫ sX ∧
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ φ = η) :
    ∃ g : X ⟶ Y, g ≫ sY = sX ∧ X.fromSpecStalk (genericPoint X) ≫ g = η := by
  classical
  choose φ hφover hφη using H
  have hspread (x : X) :=
    spread_out_of_isGermInjective' sX sY (φ x) (hφover x)
  choose U hx f hφ hf using hspread
  have hgen (x : X) : genericPoint X ∈ U x := genericPoint_mem (U x) x (hx x)
  have hfη (x : X) : (U x).fromSpecStalkOfMem (genericPoint X) (hgen x) ≫ f x = η := by
    rw [← specMap_stalkFunctionField_fromSpecStalkOfMem (U x) x (hx x),
      Category.assoc, ← hφ x]
    exact hφη x
  have hcover : IsOpenCover U := by
    change (⨆ x, U x) = ⊤
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  let 𝒰 := X.openCoverOfIsOpenCover U hcover
  have hcompat (x y : X) :
      pullback.fst (U x).ι (U y).ι ≫ f x =
        pullback.snd (U x).ι (U y).ι ≫ f y :=
    overlap_eq sX sY η (U x) (U y) (hgen x) (hgen y)
      (f x) (f y) (hf x) (hf y) (hfη x) (hfη y)
  let g : X ⟶ Y := 𝒰.glueMorphisms f hcompat
  have hg (x : X) : (U x).ι ≫ g = f x := 𝒰.ι_glueMorphisms f hcompat x
  refine ⟨g, ?_, ?_⟩
  · apply 𝒰.hom_ext
    intro x
    change X at x
    change (U x).ι ≫ g ≫ sY = (U x).ι ≫ sX
    rw [← Category.assoc, hg, hf]
  · let x : X := genericPoint X
    rw [← Scheme.Opens.fromSpecStalkOfMem_ι (U x) (genericPoint X) (hgen x),
      Category.assoc, hg]
    exact hfη x

end PiExponent.CurveStalkGluing

end OAI

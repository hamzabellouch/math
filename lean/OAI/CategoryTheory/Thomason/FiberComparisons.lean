import Mathlib
import OAI.CategoryTheory.Thomason.LabelledFibers
import OAI.CategoryTheory.Thomason.SubdivisionWeak

namespace OAI

/-! Fiber Comparisons. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

lemma oneFiberConeHomEquiv_old (p : Over interval.{u}) (B : OmegaCategory.{u})
    (F : (fiberFunctor (intervalVertex 1)).obj p ⟶ B)
    (x : ((fiberFunctor (intervalVertex 1)).obj p).Cell) :
    (oneFiberConeAdjunction.homEquiv p B F).left.map x.val = @ConeCell.old B.op (F.map x) := by
  have hx : (reverseLabel p.hom).map x.val = (intervalVertex 0).val := by
    change intervalReflect.map (p.hom.map x.val) = _
    rw [x.property]
    rfl
  let a := (reverseLabelEquivalence.toAdjunction.comp zeroFiberConeAdjunction).comp
    opEquivalence.toAdjunction
  have he := Adjunction.homEquiv_ofNatIsoLeft_apply a reversedZeroFiberNatIso F
  refine (congrArg (fun H : p ⟶ initialConeFunctor.obj B => H.left.map x.val) he).trans ?_
  dsimp only [a]
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply, zeroFiberConeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change coneExtendMap (reverseLabel p.hom)
    (Functor.comp (reversedZeroFiberIso p).hom F).op x.val = _
  exact coneExtendMap_zero _ _ _ hx

lemma oneFiberFiniteConeHomEquiv_old (n : ℕ) (hn : 1 ≤ n)
    (p : Over (finiteInterval.{u} n hn)) (B : NCategory.{u} n)
    (F : (fiberFiniteFunctor n hn 1).obj p ⟶ B)
    (x : ((fiberFiniteFunctor n hn 1).obj p).val.Cell) :
    ((oneFiberFiniteConeAdjunction n hn).homEquiv p B F).left.map x.val =
      @ConeCell.old B.val.op (F.map x) := by
  have hx : (reverseLabel p.hom).map x.val = (intervalVertex 0).val := by
    change intervalReflect.map (p.hom.map x.val) = _
    rw [x.property]
    rfl
  let a := (((reverseLabelFiniteEquivalence n hn).toAdjunction).comp
    (zeroFiberFiniteConeAdjunction n hn)).comp (opFiniteEquivalence n).toAdjunction
  have he := Adjunction.homEquiv_ofNatIsoLeft_apply a (reversedZeroFiberFiniteNatIso n hn) F
  refine (congrArg (fun H : p ⟶ (initialConeFiniteFunctor n hn).obj B => H.left.map x.val) he).trans ?_
  dsimp only [a]
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply, zeroFiberFiniteConeAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change coneExtendMap (reverseLabel p.hom)
    (Functor.comp (reversedZeroFiberFiniteIso n hn p).hom F).op x.val = _
  exact coneExtendMap_zero _ _ _ hx

lemma truncationOneFiberIso_inv_app (n : ℕ) (hn : 1 ≤ n) (p : Over interval.{u}) :
    (truncationOneFiberIso n hn).inv.app p = truncationFiberComparison n hn 1 p := by
  apply ((truncationAdjunction n).homEquiv _ _).injective
  change OmegaCategory.Functor.comp (truncationUnit n _) ((truncationOneFiberIso n hn).inv.app p) =
    OmegaCategory.Functor.comp (truncationUnit n _) (truncationFiberComparison n hn 1 p)
  rw [truncationFiberComparison_unit]
  let a := (((truncationOverAdjunction n hn).comp (oneFiberFiniteConeAdjunction n hn)).ofNatIsoRight
    (initialConeFiniteInclusionIso n hn))
  let b := oneFiberConeAdjunction.comp (truncationAdjunction n)
  have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app b a p
  change b.homEquiv p _ ((truncationOneFiberIso n hn).inv.app p) = a.unit.app p at hh
  rw [Adjunction.comp_homEquiv] at hh
  simp only [Equiv.trans_apply] at hh
  apply Functor.ext
  funext x
  have hcell := congrArg (fun H => H.left.map x.val) hh
  rw [oneFiberConeHomEquiv_old p _ _ x] at hcell
  let q := (truncationOverFunctor n hn).obj p
  have hx : q.hom.map ((truncationUnit n p.left).map x.val) = (intervalVertex 1).val := by
    have h := congrArg (fun F => F.map x.val) (Over.w ((truncationOverAdjunction n hn).unit.app p))
    exact h.trans x.property
  change ConeCell.old _ = ((oneFiberFiniteConeAdjunction n hn).unit.app q).left.map
    ((truncationUnit n p.left).map x.val) at hcell
  rw [← (oneFiberFiniteConeAdjunction n hn).homEquiv_id q] at hcell
  rw [oneFiberFiniteConeHomEquiv_old n hn q _ _ ⟨_, hx⟩] at hcell
  have h := ConeCell.old.inj hcell
  exact h

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

open CategoryTheory

lemma truncationFiberIso_inv_app (n : ℕ) (hn : 1 ≤ n) (e : Fin 2) (p : Over interval.{u}) :
    (truncationFiberIso n hn e).inv.app p = truncationFiberComparison n hn e p := by
  by_cases he : e = 0
  · subst e
    simpa only [truncationFiberIso, dite_eq_left] using truncationZeroFiberIso_inv_app n hn p
  · have he1 : e = 1 := by omega
    subst e
    simpa only [truncationFiberIso, dite_eq_right he] using truncationOneFiberIso_inv_app n hn p

lemma truncationFiberIso_inv_inclusion (n : ℕ) (hn : 1 ≤ n) (e : Fin 2)
    (p : Over interval.{u}) :
    (truncationFiberIso n hn e).inv.app p ≫
      fiberFiniteInclusion n hn e ((truncationOverFunctor n hn).obj p) =
      (truncationFunctor n).map (p.hom.fiber (intervalVertex e)).inclusion := by
  rw [truncationFiberIso_inv_app]
  exact truncationFiberComparison_inclusion n hn e p

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains.PosetTables

open CategoryTheory OmegaCategory DirectedComplex

variable {P : Type u} [PartialOrder P]

lemma truncationTableFiberIso_inclusion (n : ℕ) (hn : 1 ≤ n) (f : P →o Fin 2) (e : Fin 2) :
    (truncationTableFiberIso n hn f e).hom ≫
      fiberFiniteInclusion n hn e ((truncationOverFunctor n hn).obj (Over.mk (tableLabel f))) =
      (truncationFunctor n).map
        (complexMap (OrderEmbedding.subtype {a | f a = e}).toOrderHom).nu := by
  apply truncation_functor_ext
  apply OmegaCategory.Functor.ext
  funext x
  have h := congrArg (fun F => F.map ((tableFiberSegmentIso f e).hom.map x))
    (truncationFiberComparison_unit n hn e (Over.mk (tableLabel f)))
  rw [← truncationFiberIso_inv_app] at h
  exact congrArg Subtype.val h

end Thomason.NormalizedChains.PosetTables

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory CategoryTheory.Limits OmegaCategory

noncomputable def categorificationSimplexDiagram (X : SSet.{u}) :
    CostructuredArrow uliftYoneda.{u,0,0} X ⥤ OmegaCategory.{u} :=
  CostructuredArrow.proj uliftYoneda.{u,0,0} X ⋙ raisedOrientals

noncomputable def categorificationSimplexCocone (X : SSet.{u}) :
    Cocone (categorificationSimplexDiagram X) :=
  (CategoryTheory.Functor.LeftExtension.mk categorification
    ((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
      raisedOrientals.{u})).coconeAt X

noncomputable def categorificationSimplexIsColimit (X : SSet.{u}) :
    IsColimit (categorificationSimplexCocone X) := by
  unfold categorificationSimplexCocone categorification
  exact CategoryTheory.Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ _ X

noncomputable def categorificationFiniteSimplexIsColimit (n : ℕ) (X : SSet.{u}) :
    IsColimit ((truncationFunctor n).mapCocone (categorificationSimplexCocone X)) :=
  isColimitOfPreserves (truncationFunctor n) (categorificationSimplexIsColimit X)

noncomputable def labelledSimplexIsColimit (X : SSet.{u})
    (p : categorification.obj X ⟶ interval.{u}) :
    IsColimit (Over.liftCocone (categorificationSimplexCocone X) p) :=
  Over.isColimitLiftCocone _ p (categorificationSimplexIsColimit X)

noncomputable def labelledSimplexFiberIsColimit (X : SSet.{u})
    (p : categorification.obj X ⟶ interval.{u}) (e : Fin 2) :
    IsColimit ((fiberFunctor (intervalVertex e)).mapCocone
      (Over.liftCocone (categorificationSimplexCocone X) p)) := by
  have : PreservesColimitsOfSize.{0,u} (fiberFunctor.{u} (intervalVertex e)) := by
    by_cases he : e = 0
    · subst e; infer_instance
    · have he1 : e = 1 := by omega
      subst e; infer_instance
  exact isColimitOfPreserves (fiberFunctor (intervalVertex e)) (labelledSimplexIsColimit X p)

noncomputable def labelledFiniteSimplexIsColimit (n : ℕ) (hn : 1 ≤ n) (X : SSet.{u})
    (p : (categorificationFinite n).obj X ⟶ finiteInterval.{u} n hn) :
    IsColimit (Over.liftCocone
      ((truncationFunctor n).mapCocone (categorificationSimplexCocone X)) p) :=
  Over.isColimitLiftCocone _ p (categorificationFiniteSimplexIsColimit n X)

noncomputable def labelledFiniteSimplexFiberIsColimit (n : ℕ) (hn : 1 ≤ n) (X : SSet.{u})
    (p : (categorificationFinite n).obj X ⟶ finiteInterval.{u} n hn) (e : Fin 2) :
    IsColimit ((fiberFiniteFunctor n hn e).mapCocone
      (Over.liftCocone ((truncationFunctor n).mapCocone (categorificationSimplexCocone X)) p)) := by
  have : PreservesColimitsOfSize.{0,u} (fiberFiniteFunctor.{u} n hn e) := by
    by_cases he : e = 0
    · subst e; infer_instance
    · have he1 : e = 1 := by omega
      subst e; infer_instance
  exact isColimitOfPreserves (fiberFiniteFunctor n hn e)
    (labelledFiniteSimplexIsColimit n hn X p)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite NormalizedChains NormalizedChains.PosetTables OmegaCategory

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def posetSimplexOrder {m : SimplexCategoryᵒᵖ} (s : (nerve P).obj m) :
    Fin (m.unop.len+1) →o P := ⟨s.obj, s.monotone⟩

noncomputable def posetTableNerveMap (P : Type u) [PartialOrder P] :
    nerve P ⟶ streetNerve (complex P).nu where
  app _ := ↾fun s => (complexMap (posetSimplexOrder s)).nu
  naturality m n f := by
    apply ConcreteCategory.hom_ext
    intro s
    change (complexMap ((posetSimplexOrder s).comp f.unop.toOrderHom)).nu =
      (DirectedComplex.Hom.comp (complexMap f.unop.toOrderHom)
        (complexMap (posetSimplexOrder s))).nu
    exact congrArg DirectedComplex.Hom.nu (complexMap_comp _ _)

lemma posetTableNerveMap_natural (f : P →o Q) :
    nerveMap f.monotone.functor ≫ posetTableNerveMap Q =
      posetTableNerveMap P ≫ streetNerveMap (complexMap f).nu := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro s
  change (complexMap (f.comp (posetSimplexOrder s))).nu =
    (DirectedComplex.Hom.comp (complexMap (posetSimplexOrder s)) (complexMap f)).nu
  exact congrArg DirectedComplex.Hom.nu (complexMap_comp _ _)

noncomputable def posetCategorificationTableMap (P : Type u) [PartialOrder P] :
    categorification.obj (nerve P) ⟶ (complex P).nu :=
  (categorificationAdjunction.homEquiv _ _).symm (posetTableNerveMap P)

lemma posetCategorificationTableMap_natural (f : P →o Q) :
    categorification.map (nerveMap f.monotone.functor) ≫ posetCategorificationTableMap Q =
      posetCategorificationTableMap P ≫ (complexMap f).nu := by
  calc
    _ = (categorificationAdjunction.homEquiv _ _).symm
        (nerveMap f.monotone.functor ≫ posetTableNerveMap Q) :=
      (categorificationAdjunction.homEquiv_naturality_left_symm
        (nerveMap f.monotone.functor) (posetTableNerveMap Q)).symm
    _ = (categorificationAdjunction.homEquiv _ _).symm
        (posetTableNerveMap P ≫ streetNerveFunctor.map (complexMap f).nu) :=
      congrArg (categorificationAdjunction.homEquiv _ _).symm
        (posetTableNerveMap_natural f)
    _ = _ := categorificationAdjunction.homEquiv_naturality_right_symm
      (posetTableNerveMap P) (complexMap f).nu

noncomputable def posetCategorificationLabel (f : P →o Fin 2) :
    categorification.obj (nerve P) ⟶ interval.{u} :=
  posetCategorificationTableMap P ≫ tableLabel f

lemma posetCategorificationLabel_natural (g : P →o Q) (f : Q →o Fin 2) :
    categorification.map (nerveMap g.monotone.functor) ≫ posetCategorificationLabel f =
      posetCategorificationLabel (f.comp g) := by
  unfold posetCategorificationLabel
  rw [← Category.assoc, posetCategorificationTableMap_natural, Category.assoc]
  exact congrArg (fun F => posetCategorificationTableMap P ≫ F) (tableLabel_natural g f)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Opposite OmegaCategory NormalizedChains NormalizedChains.PosetTables

lemma categorification_homEquiv_app {X : SSet.{u}} {C : OmegaCategory.{u}}
    (F : categorification.obj X ⟶ C) {m : SimplexCategoryᵒᵖ} (s : X.obj m) :
    (categorificationAdjunction.homEquiv X C F).app m s =
      OmegaCategory.Functor.comp (uliftUp _) 
        ((categorificationSimplexCocone X).ι.app
          (CostructuredArrow.mk (uliftYonedaEquiv.symm s)) ≫ F) := by
  let L := (uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtension raisedOrientals
  let α := (uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit raisedOrientals
  calc
    _ = streetYonedaEquiv C m
        (((Presheaf.uliftYonedaAdjunction.{0} L α).homEquiv X C F).app m s) := by
      exact congrArg (fun t => t.app m s)
        (Adjunction.homEquiv_ofNatIsoRight_apply
          (Presheaf.uliftYonedaAdjunction.{0} L α) streetYonedaIso F)
    _ = _ := congrArg (streetYonedaEquiv C m)
      (Presheaf.uliftYonedaAdjunction_homEquiv_app L α F s)

lemma posetCategorificationTableMap_leg {P : Type u} [PartialOrder P]
    {m : SimplexCategoryᵒᵖ} (s : (nerve P).obj m) :
    (categorificationSimplexCocone (nerve P)).ι.app
        (CostructuredArrow.mk (uliftYonedaEquiv.symm s)) ≫
      posetCategorificationTableMap P =
      OmegaCategory.Functor.comp (uliftDown _) (complexMap (posetSimplexOrder s)).nu := by
  have h := congrArg (fun t => t.app m s)
    ((categorificationAdjunction.homEquiv _ _).apply_symm_apply (posetTableNerveMap P))
  have hg := categorification_homEquiv_app (posetCategorificationTableMap P) s
  have he : OmegaCategory.Functor.comp (uliftUp _)
      ((categorificationSimplexCocone (nerve P)).ι.app
        (CostructuredArrow.mk (uliftYonedaEquiv.symm s)) ≫ posetCategorificationTableMap P) =
      (complexMap (posetSimplexOrder s)).nu := hg.symm.trans h
  exact congrArg (fun F => OmegaCategory.Functor.comp (uliftDown _) F) he

lemma posetCategorificationTableMap_leg_lifted {P : Type u} [PartialOrder P]
    {m : SimplexCategoryᵒᵖ} (s : (nerve P).obj m) :
    (categorificationSimplexCocone (nerve P)).ι.app
        (CostructuredArrow.mk (uliftYonedaEquiv.symm s)) ≫
      posetCategorificationTableMap P =
      (complexULiftIso.{0,u} (Fin (m.unop.len+1))).hom ≫
        (complexMap ((posetSimplexOrder s).comp (orderULiftDown _))).nu := by
  rw [posetCategorificationTableMap_leg]
  have h := congrArg DirectedComplex.Hom.nu
    (complexMap_comp (orderULiftUp.{0,u} (Fin (m.unop.len+1)))
      ((posetSimplexOrder s).comp (orderULiftDown _)))
  exact congrArg (fun F => OmegaCategory.Functor.comp (uliftDown _) F) h

lemma posetCategorificationLabel_leg {P : Type u} [PartialOrder P]
    (f : P →o Fin 2) {m : SimplexCategoryᵒᵖ} (s : (nerve P).obj m) :
    (categorificationSimplexCocone (nerve P)).ι.app
        (CostructuredArrow.mk (uliftYonedaEquiv.symm s)) ≫
      posetCategorificationLabel f =
      (complexULiftIso.{0,u} (Fin (m.unop.len+1))).hom ≫
        tableLabel (f.comp ((posetSimplexOrder s).comp (orderULiftDown _))) := by
  have h := congrArg (fun F => F ≫ tableLabel f)
    (posetCategorificationTableMap_leg_lifted s)
  exact h.trans (congrArg
    (fun F => (complexULiftIso.{0,u} (Fin (m.unop.len+1))).hom ≫ F)
    (tableLabel_natural ((posetSimplexOrder s).comp (orderULiftDown _)) f))

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Simplicial Opposite OmegaCategory NormalizedChains NormalizedChains.PosetTables

instance categorificationSimplexLeg_isIso {X : SSet.{u}} {m : SimplexCategoryᵒᵖ}
    (s : X.obj m) [IsIso (uliftYonedaEquiv.symm s)] :
    IsIso ((categorificationSimplexCocone X).ι.app
      (CostructuredArrow.mk (uliftYonedaEquiv.symm s))) := by
  change IsIso (((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
    raisedOrientals).app m.unop ≫ categorification.map (uliftYonedaEquiv.symm s))
  have h₁ : IsIso (((uliftYoneda.{u} : SimplexCategory ⥤ SSet.{u}).leftKanExtensionUnit
    raisedOrientals).app m.unop) := (categorificationSimplexIso.{u} m.unop).isIso_inv
  have h₂ : IsIso (categorification.map (uliftYonedaEquiv.symm s)) := inferInstance
  exact IsIso.comp_isIso' h₁ h₂

noncomputable instance posetCategorificationTableMap_ordinal_isIso (n : ℕ) :
    IsIso (posetCategorificationTableMap (ULift.{u} (Fin (n+1)))) := by
  let s : (nerve (ULift.{u} (Fin (n+1)))).obj (op ⦋n⦌) :=
    uliftYonedaEquiv (SSet.stdSimplex.isoNerve.{u} n).hom
  have hs : posetSimplexOrder s = orderULiftUp.{0,u} (Fin (n+1)) := by
    ext i
    rfl
  have hi : IsIso (uliftYonedaEquiv.symm s) := by
    have hh : uliftYonedaEquiv.symm s = (SSet.stdSimplex.isoNerve.{u} n).hom :=
      uliftYonedaEquiv.symm_apply_apply _
    exact hh ▸ (SSet.stdSimplex.isoNerve.{u} n).isIso_hom
  let leg := (categorificationSimplexCocone (nerve (ULift.{u} (Fin (n+1))))).ι.app
    (CostructuredArrow.mk (uliftYonedaEquiv.symm s))
  have he : leg ≫ posetCategorificationTableMap (ULift.{u} (Fin (n+1))) =
      (complexULiftIso.{0,u} (Fin (n+1))).hom := by
    have h := posetCategorificationTableMap_leg s
    rw [hs] at h
    exact h
  have hleg : IsIso leg := categorificationSimplexLeg_isIso s
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ hleg
    (complexULiftIso.{0,u} (Fin (n+1))).isIso_hom he

noncomputable def posetComplexFunctor : PartOrd.{u} ⥤ DirectedComplex.{u} where
  obj P := complex P
  map f := complexMap f.hom
  map_id _ := complexMap_id
  map_comp f g := complexMap_comp f.hom g.hom

lemma posetCategorificationTableMap_isIso_of_orderIso
    {P Q : Type u} [PartialOrder P] [PartialOrder Q] (e : P ≃o Q)
    [IsIso (posetCategorificationTableMap P)] :
    IsIso (posetCategorificationTableMap Q) := by
  have hN : IsIso (nerveMap e.toOrderEmbedding.toOrderHom.monotone.functor) :=
    (PartOrd.nerveFunctor.mapIso (PartOrd.Iso.mk (α := PartOrd.of P) (β := PartOrd.of Q) e)).isIso_hom
  have hT : IsIso (show (complex P).nu ⟶ (complex Q).nu from
      (complexMap e.toOrderEmbedding.toOrderHom).nu) :=
    ((posetComplexFunctor ⋙ DirectedComplex.nuFunctor).mapIso
      (PartOrd.Iso.mk (α := PartOrd.of P) (β := PartOrd.of Q) e)).isIso_hom
  have h := posetCategorificationTableMap_natural e.toOrderEmbedding.toOrderHom
  exact IsIso.of_isIso_fac_left h

theorem posetCategorificationTableMap_finiteLinear_isIso
    (P : Type u) [LinearOrder P] [Finite P] [Nonempty P] :
    IsIso (posetCategorificationTableMap P) := by
  classical
  let := Fintype.ofFinite P
  let n := Fintype.card P - 1
  have hn : Fintype.card P = n+1 := by
    have := Fintype.card_pos (α := P)
    dsimp only [n]
    omega
  let e : ULift.{u} (Fin (n+1)) ≃o P :=
    ULift.orderIso.trans (Fintype.orderIsoFinOfCardEq P hn)
  exact posetCategorificationTableMap_isIso_of_orderIso e

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory Limits OmegaCategory NormalizedChains NormalizedChains.PosetTables

noncomputable def emptyOmegaIsInitial (C : OmegaCategory.{u}) [IsEmpty C.Cell] : IsInitial C :=
  IsInitial.ofUniqueHom
    (fun D => { map := isEmptyElim
                map_source := fun _ x => isEmptyElim x
                map_target := fun _ x => isEmptyElim x
                map_comp := fun _ x => isEmptyElim x })
    (fun _ F => by
      apply OmegaCategory.Functor.ext
      funext x
      exact isEmptyElim x)

noncomputable def emptyPosetNerveIsInitial (P : Type u) [PartialOrder P] [IsEmpty P] :
    IsInitial (nerve P) :=
  IsInitial.ofUniqueHom
    (fun X => {
      app := fun _ => ↾fun s => isEmptyElim (s.obj 0)
      naturality := fun _ _ _ => by
        apply ConcreteCategory.hom_ext
        intro s
        exact isEmptyElim (s.obj 0) })
    (fun _ F => by
      apply NatTrans.ext
      funext m
      apply ConcreteCategory.hom_ext
      intro s
      exact isEmptyElim (s.obj 0))

theorem posetCategorificationTableMap_empty_isIso (P : Type u) [PartialOrder P] [IsEmpty P] :
    IsIso (posetCategorificationTableMap P) := by
  have : IsEmpty (complex P).nu.Cell := ⟨fun x => isEmptyElim (tableStart x)⟩
  exact isIso_of_isInitial
    ((emptyPosetNerveIsInitial P).isInitialObj categorification (nerve P))
    (emptyOmegaIsInitial (complex P).nu) _

theorem posetCategorificationTableMap_finiteLinear_isIso_all
    (P : Type u) [LinearOrder P] [Finite P] :
    IsIso (posetCategorificationTableMap P) := by
  cases isEmpty_or_nonempty P with
  | inl h => exact posetCategorificationTableMap_empty_isIso P
  | inr h => exact posetCategorificationTableMap_finiteLinear_isIso P

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

variable {P : Type u} [PartialOrder P]

def posetLevelInclusion (f : P →o Fin 2) (e : Fin 2) : {a // f a = e} →o P :=
  (OrderEmbedding.subtype {a | f a = e}).toOrderHom

lemma posetCategorification_level_mem (f : P →o Fin 2) (e : Fin 2)
    (x : (categorification.obj (nerve {a // f a = e})).Cell) :
    (posetCategorificationLabel f).map
      ((categorification.map (nerveMap (posetLevelInclusion f e).monotone.functor)).map x) =
      (intervalVertex e).val := by
  have h := congrArg (fun F => F.map x)
    (posetCategorificationLabel_natural (posetLevelInclusion f e) f)
  apply h.trans
  apply ThinCell.ext
  · apply ULift.ext
    exact (tableStart ((posetCategorificationTableMap {a // f a = e}).map x)).property
  · apply ULift.ext
    exact (tableFinish ((posetCategorificationTableMap {a // f a = e}).map x)).property

noncomputable def posetCategorificationFiberMap (f : P →o Fin 2) (e : Fin 2) :
    categorification.obj (nerve {a // f a = e}) ⟶
      ((posetCategorificationLabel f).fiber (intervalVertex e)).category :=
  ((posetCategorificationLabel f).fiber (intervalVertex e)).lift
    (categorification.map (nerveMap (posetLevelInclusion f e).monotone.functor))
      (posetCategorification_level_mem f e)

lemma posetCategorificationFiberMap_inclusion (f : P →o Fin 2) (e : Fin 2) :
    posetCategorificationFiberMap f e ≫
      ((posetCategorificationLabel f).fiber (intervalVertex e)).inclusion =
      categorification.map (nerveMap (posetLevelInclusion f e).monotone.functor) := rfl

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

variable {P : Type u} [PartialOrder P]

noncomputable def posetCategorificationTableOver (f : P →o Fin 2) :
    Over.mk (posetCategorificationLabel f) ⟶ Over.mk (tableLabel f) :=
  Over.homMk (posetCategorificationTableMap P) rfl

noncomputable def posetCategorificationTableFiberMap (f : P →o Fin 2) (e : Fin 2) :
    ((posetCategorificationLabel f).fiber (intervalVertex e)).category ⟶
      ((tableLabel f).fiber (intervalVertex e)).category :=
  (fiberFunctor (intervalVertex e)).map (posetCategorificationTableOver f)

lemma posetCategorificationFiberMap_table_fac (f : P →o Fin 2) (e : Fin 2) :
    posetCategorificationFiberMap f e ≫ posetCategorificationTableFiberMap f e =
      posetCategorificationTableMap {a // f a = e} ≫ (tableFiberSegmentIso f e).hom := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  exact congrArg (fun F => F.map x)
    (posetCategorificationTableMap_natural (posetLevelInclusion f e))

theorem posetCategorificationFiberMap_finiteLinear_isIso (P : Type u)
    [LinearOrder P] [Finite P] (f : P →o Fin 2) (e : Fin 2) :
    IsIso (posetCategorificationFiberMap f e) := by
  have hP := posetCategorificationTableMap_finiteLinear_isIso_all P
  have hS := posetCategorificationTableMap_finiteLinear_isIso_all {a // f a = e}
  have hForget : IsIso ((Over.forget interval).map (posetCategorificationTableOver f)) := hP
  have hO : IsIso (posetCategorificationTableOver f) :=
    isIso_of_reflects_iso _ (Over.forget _)
  have hF : IsIso (posetCategorificationTableFiberMap f e) :=
    CategoryTheory.Functor.map_isIso _ _
  have hT : IsIso (posetCategorificationTableMap {a // f a = e} ≫
      (tableFiberSegmentIso f e).hom) := IsIso.comp_isIso' hS (tableFiberSegmentIso f e).isIso_hom
  exact IsIso.of_isIso_fac_right (posetCategorificationFiberMap_table_fac f e)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

variable {P : Type u} [PartialOrder P]

noncomputable def posetCategorificationFiniteFiberMap (n : ℕ) (hn : 1 ≤ n)
    (f : P →o Fin 2) (e : Fin 2) :
    (categorificationFinite n).obj (nerve {a // f a = e}) ⟶
      (fiberFiniteFunctor n hn e).obj
        ((truncationOverFunctor n hn).obj (Over.mk (posetCategorificationLabel f))) :=
  (truncationFunctor n).map (posetCategorificationFiberMap f e) ≫
    (truncationFiberIso n hn e).inv.app (Over.mk (posetCategorificationLabel f))

lemma posetCategorificationFiniteFiberMap_inclusion (n : ℕ) (hn : 1 ≤ n)
    (f : P →o Fin 2) (e : Fin 2) :
    posetCategorificationFiniteFiberMap n hn f e ≫
      fiberFiniteInclusion n hn e
        ((truncationOverFunctor n hn).obj (Over.mk (posetCategorificationLabel f))) =
      (categorificationFinite n).map
        (nerveMap (posetLevelInclusion f e).monotone.functor) := by
  have h := congrArg (fun F => (truncationFunctor n).map
    (posetCategorificationFiberMap f e) ≫ F)
      (truncationFiberIso_inv_inclusion n hn e (Over.mk (posetCategorificationLabel f)))
  exact h.trans (((truncationFunctor n).map_comp _ _).symm.trans
    (congrArg (truncationFunctor n).map (posetCategorificationFiberMap_inclusion f e)))

theorem posetCategorificationFiniteFiberMap_finiteLinear_isIso (n : ℕ) (hn : 1 ≤ n)
    (P : Type u) [LinearOrder P] [Finite P] (f : P →o Fin 2) (e : Fin 2) :
    IsIso (posetCategorificationFiniteFiberMap n hn f e) := by
  have := posetCategorificationFiberMap_finiteLinear_isIso P f e
  unfold posetCategorificationFiniteFiberMap
  exact IsIso.comp_isIso'
    (CategoryTheory.Functor.map_isIso _ _)
    ((truncationFiberIso n hn e).app (Over.mk (posetCategorificationLabel f))).isIso_inv

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

def posetLevelMap (g : P →o Q) (f : Q →o Fin 2) (e : Fin 2) :
    {a // (f.comp g) a = e} →o {b // f b = e} where
  toFun a := ⟨g a.val, a.property⟩
  monotone' := fun _ _ h => g.monotone h

lemma posetLevelMap_inclusion (g : P →o Q) (f : Q →o Fin 2) (e : Fin 2) :
    (posetLevelInclusion f e).comp (posetLevelMap g f e) =
      g.comp (posetLevelInclusion (f.comp g) e) := rfl

noncomputable def posetCategorificationOverMap (g : P →o Q) (f : Q →o Fin 2) :
    Over.mk (posetCategorificationLabel (f.comp g)) ⟶
      Over.mk (posetCategorificationLabel f) :=
  Over.homMk (categorification.map (nerveMap g.monotone.functor))
    (posetCategorificationLabel_natural g f)

lemma posetCategorificationFiberMap_natural (g : P →o Q) (f : Q →o Fin 2) (e : Fin 2) :
    categorification.map (nerveMap (posetLevelMap g f e).monotone.functor) ≫
      posetCategorificationFiberMap f e =
    posetCategorificationFiberMap (f.comp g) e ≫
      (fiberFunctor (intervalVertex e)).map (posetCategorificationOverMap g f) := by
  apply OmegaCategory.Functor.ext
  funext x
  apply Subtype.ext
  change ((categorification.map (nerveMap (posetLevelMap g f e).monotone.functor) ≫
    categorification.map (nerveMap (posetLevelInclusion f e).monotone.functor)).map x) =
    ((categorification.map (nerveMap (posetLevelInclusion (f.comp g) e).monotone.functor) ≫
      categorification.map (nerveMap g.monotone.functor)).map x)
  apply congrArg (fun (F : categorification.obj (nerve {a // (f.comp g) a = e}) ⟶
    categorification.obj (nerve Q)) => F.map x)
  rw [← categorification.map_comp, ← categorification.map_comp]
  apply congrArg categorification.map
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  rfl

lemma posetCategorificationFiniteFiberMap_natural (n : ℕ) (hn : 1 ≤ n)
    (g : P →o Q) (f : Q →o Fin 2) (e : Fin 2) :
    (categorificationFinite n).map (nerveMap (posetLevelMap g f e).monotone.functor) ≫
      posetCategorificationFiniteFiberMap n hn f e =
    posetCategorificationFiniteFiberMap n hn (f.comp g) e ≫
      (fiberFiniteFunctor n hn e).map
        ((truncationOverFunctor n hn).map (posetCategorificationOverMap g f)) := by
  let T := truncationFunctor n
  let a := categorification.map (nerveMap (posetLevelMap g f e).monotone.functor)
  let b := posetCategorificationFiberMap f e
  let c := posetCategorificationFiberMap (f.comp g) e
  let d := (fiberFunctor (intervalVertex e)).map (posetCategorificationOverMap g f)
  let i := (truncationFiberIso n hn e).inv.app (Over.mk (posetCategorificationLabel f))
  let j := (truncationFiberIso n hn e).inv.app
    (Over.mk (posetCategorificationLabel (f.comp g)))
  let k := (fiberFiniteFunctor n hn e).map
    ((truncationOverFunctor n hn).map (posetCategorificationOverMap g f))
  have hab : a ≫ b = c ≫ d := posetCategorificationFiberMap_natural g f e
  have h : T.map d ≫ i = j ≫ k :=
    (truncationFiberIso n hn e).inv.naturality (posetCategorificationOverMap g f)
  change T.map a ≫ (T.map b ≫ i) = (T.map c ≫ j) ≫ k
  calc
    _ = (T.map a ≫ T.map b) ≫ i := (Category.assoc _ _ _).symm
    _ = T.map (a ≫ b) ≫ i := congrArg (fun F => F ≫ i) (T.map_comp a b).symm
    _ = T.map (c ≫ d) ≫ i := congrArg (fun F => T.map F ≫ i) hab
    _ = (T.map c ≫ T.map d) ≫ i := congrArg (fun F => F ≫ i) (T.map_comp c d)
    _ = T.map c ≫ (T.map d ≫ i) := Category.assoc _ _ _
    _ = T.map c ≫ (j ≫ k) := congrArg (fun F => T.map c ≫ F) h
    _ = _ := (Category.assoc _ _ _).symm

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason

open CategoryTheory OmegaCategory NormalizedChains NormalizedChains.PosetTables

noncomputable def posetCategorificationFiberIsoFinite
    (P : Type u) [LinearOrder P] [Finite P] (f : P →o Fin 2) (e : Fin 2) :
    categorification.obj (nerve {a // f a = e}) ≅
      ((posetCategorificationLabel f).fiber (intervalVertex e)).category := by
  have h : IsIso (posetCategorificationFiberMap f e) :=
    posetCategorificationFiberMap_finiteLinear_isIso P f e
  exact asIso (posetCategorificationFiberMap f e)

lemma posetCategorificationFiberIsoFinite_hom
    (P : Type u) [LinearOrder P] [Finite P] (f : P →o Fin 2) (e : Fin 2) :
    (posetCategorificationFiberIsoFinite P f e).hom = posetCategorificationFiberMap f e := rfl

lemma posetCategorificationFiberMap_inverse_natural
    {P Q : Type u} [LinearOrder P] [LinearOrder Q] [Finite P] [Finite Q]
    (g : P →o Q) (f : Q →o Fin 2) (e : Fin 2) :
    (fiberFunctor (intervalVertex e)).map (posetCategorificationOverMap g f) ≫
      (posetCategorificationFiberIsoFinite Q f e).inv =
    (posetCategorificationFiberIsoFinite P (f.comp g) e).inv ≫
      categorification.map (nerveMap (posetLevelMap g f e).monotone.functor) := by
  apply (Iso.eq_inv_comp (posetCategorificationFiberIsoFinite P (f.comp g) e)).mpr
  exact (Category.assoc (posetCategorificationFiberIsoFinite P (f.comp g) e).hom
    ((fiberFunctor (intervalVertex e)).map (posetCategorificationOverMap g f))
    (posetCategorificationFiberIsoFinite Q f e).inv).symm.trans
      ((Iso.comp_inv_eq (posetCategorificationFiberIsoFinite Q f e)).mpr
        (posetCategorificationFiberMap_natural g f e).symm)

end Thomason

end

end OAI

import OAI.Algebra.AuslanderReiten.HomComplex.FullHomComparison

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u

section Cochains

variable {C : Type*} [Category* C] [Preadditive C]
variable {K L M : CochainComplex C ℤ} {n m : ℤ}

def cocycleProduct (x : Cocycle K L n) (y : Cocycle L M m) : Cocycle K M (n + m) :=
  Cocycle.mk (x.1.comp y.1 rfl) _ rfl (by
    rw [δ_comp x.1 y.1 rfl (n + 1) (m + 1) (n + m + 1) rfl rfl rfl]
    simp)

@[simp]
theorem cocycleProduct_coe (x : Cocycle K L n) (y : Cocycle L M m) :
    (cocycleProduct x y).1 = x.1.comp y.1 rfl := rfl

def shiftedCocycleHom (y : Cocycle L M m) (n : ℤ) : L⟦n⟧ ⟶ M⟦n + m⟧ :=
  (Cocycle.equivHomShift.symm y)⟦n⟧' ≫
    (CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) m n (n + m)
      (add_comm m n)).inv.app M

theorem cocycleHom_component (x : Cocycle K L n) (i : ℤ) :
    (Cocycle.equivHomShift.symm x).f i = x.1.v i (i + n) rfl := by
  simp only [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
    Cocycle.rightShift_coe, Cochain.rightShift_v, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv]
  exact Category.comp_id _

private theorem cochain_component_transport (x : Cochain K L n)
    (p q r : ℤ) (hpq : p + n = q) (hqr : q = r) :
    x.v p q hpq ≫ (L.XIsoOfEq hqr).hom = x.v p r (hpq.trans hqr) := by
  subst r
  simp

theorem cocycleHom_product (x : Cocycle K L n) (y : Cocycle L M m) :
    Cocycle.equivHomShift.symm (cocycleProduct x y) =
      Cocycle.equivHomShift.symm x ≫ shiftedCocycleHom y n := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f, shiftedCocycleHom, cocycleHom_component,
    shiftFunctor_map_f', shiftFunctorAdd'_inv_app_f']
  change (x.1.comp y.1 rfl).v i (i + (n + m)) rfl =
    x.1.v i (i + n) rfl ≫ y.1.v (i + n) (i + n + m) rfl ≫
      (M.XIsoOfEq (show i + n + m = i + (n + m) by omega)).hom
  rw [cochain_component_transport]
  exact Cochain.comp_v x.1 y.1 rfl i (i + n) (i + (n + m)) rfl (by omega)

theorem cocycleProduct_respects_classes
    (x x' : Cocycle K L n) (y y' : Cocycle L M m)
    (hx : CohomologyClass.mk x = CohomologyClass.mk x')
    (hy : CohomologyClass.mk y = CohomologyClass.mk y') :
    CohomologyClass.mk (cocycleProduct x y) = CohomologyClass.mk (cocycleProduct x' y') := by
  have hx' := congrArg CohomologyClass.toHom hx
  have hy' := congrArg CohomologyClass.toHom hy
  let Hx := HomotopyCategory.homotopyOfEq _ _ hx'
  let Hy := HomotopyCategory.homotopyOfEq _ _ hy'
  apply (CohomologyClass.toHom_bijective K M (n + m)).1
  change (HomotopyCategory.quotient _ _).map
      (Cocycle.equivHomShift.symm (cocycleProduct x y)) =
    (HomotopyCategory.quotient _ _).map (Cocycle.equivHomShift.symm (cocycleProduct x' y'))
  rw [cocycleHom_product, cocycleHom_product]
  exact HomotopyCategory.eq_of_homotopy _ _ (Hx.comp ((Hy.shift n).compRight _))

def fullHomProduct (x : CohomologyClass K L n) (y : CohomologyClass L M m) :
    CohomologyClass K M (n + m) :=
  Quotient.liftOn₂ x y (fun a b => CohomologyClass.mk (cocycleProduct a b)) (by
    intro a b a' b' ha hb
    exact cocycleProduct_respects_classes a a' b b' (Quotient.sound ha) (Quotient.sound hb))

@[simp]
theorem fullHomProduct_mk (x : Cocycle K L n) (y : Cocycle L M m) :
    fullHomProduct (CohomologyClass.mk x) (CohomologyClass.mk y) =
      CohomologyClass.mk (cocycleProduct x y) := rfl

end Cochains

variable {R : Type u} [Ring R]
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ} {n m : ℤ}

noncomputable def cocycleComparisonMap (x : Cocycle K L n) :
    chainOfCochain K ⟶ chainOfCochain (L⟦n⟧) :=
  HomologicalComplex.extendMap (Cocycle.equivHomShift.symm x) negIndexEmbedding

@[simp]
theorem fullHomStableEquiv_mk (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain (L⟦n⟧))) (x : Cocycle K L n) :
    fullHomStableEquiv K L n hK hL (CohomologyClass.mk x) =
      StableHom.classOf R _ _ (cokernelMap (cocycleComparisonMap x) 0) := by
  exact homotopyCokernelEquiv_map hK hL (cocycleComparisonMap x)

theorem fullHomStableEquiv_product
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain (L⟦n⟧)))
    (hM : ExactProjectiveComplex (chainOfCochain (M⟦n + m⟧)))
    (x : Cocycle K L n) (y : Cocycle L M m) :
    fullHomStableEquiv K M (n + m) hK hM (CohomologyClass.mk (cocycleProduct x y)) =
      StableHom.comp
        (StableHom.classOf R _ _ (cokernelMap
          (HomologicalComplex.extendMap (shiftedCocycleHom y n) negIndexEmbedding) 0))
        (fullHomStableEquiv K L n hK hL (CohomologyClass.mk x)) := by
  rw [fullHomStableEquiv_mk, fullHomStableEquiv_mk, StableHom.comp_classOf]
  unfold cocycleComparisonMap
  rw [cocycleHom_product, HomologicalComplex.extendMap_comp, cokernelMap_comp]

end ArExplicit.CompleteComparison

end OAI

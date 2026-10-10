import Mathlib
import OAI.GroupTheory.FiniteType.PartialResolutionPartialCyclesFg

namespace OAI

noncomputable section

section
namespace SingularAction
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CategoryTheory HomologicalComplex ProductCriterion
variable {G X : Type} [Group G] [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]

def actionMap (g : G) : C(X,X) := ⟨(g • ·),continuous_const_smul g⟩
def rep (j : ℕ) : Rep ℤ G :=
  Rep.of ({ toFun := fun g => (homologyMap (SingularChains.map (actionMap (X:=X) g)) j).hom
            map_one' := by
              have he : actionMap (X:=X) (1:G) = ContinuousMap.id _ := by
                ext x; simp [actionMap]
              rw [he,SingularChains.map_id,homologyMap_id]
              rfl
            map_mul' := by
              intro g h
              have he : actionMap (X:=X) (g*h) = (actionMap g).comp (actionMap h) := by
                ext x; simp [actionMap,mul_smul]
              rw [he,SingularChains.map_comp,homologyMap_comp]
              rfl } : Representation ℤ G ((SingularChains.chains X).homology j))

def val : C((univ : Set X),X) := ⟨Subtype.val,continuous_subtype_val⟩
def ofVal : C(X,(univ : Set X)) := ⟨fun x => ⟨x,mem_univ x⟩,continuous_id.subtype_mk _⟩

lemma val_surjective (j : ℕ) :
    Function.Surjective (homologyMap (SingularChains.map (val (X:=X))) j) := by
  intro x
  refine ⟨homologyMap (SingularChains.map (ofVal (X:=X))) j x,?_⟩
  change (homologyMap (SingularChains.map (ofVal (X:=X))) j ≫
    homologyMap (SingularChains.map (val (X:=X))) j) x = x
  rw [← homologyMap_comp,← SingularChains.map_comp]
  have he : (val (X:=X)).comp ofVal = ContinuousMap.id X := rfl
  rw [he,SingularChains.map_id,homologyMap_id]
  rfl

def fromUniv (j : ℕ) : CWEquivariant.wholeRep (G:=G) (X:=X) j ⟶ rep (G:=G) (X:=X) j :=
  Rep.ofHom ((homologyMap (SingularChains.map (val (X:=X))) j).hom.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    change (homologyMap (SingularChains.map (CWEquivariant.onSpace g)) j ≫
      homologyMap (SingularChains.map val) j) x =
      (homologyMap (SingularChains.map val) j ≫ homologyMap (SingularChains.map (actionMap g)) j) x
    rw [← homologyMap_comp,← homologyMap_comp,← SingularChains.map_comp,← SingularChains.map_comp]
    rfl))

lemma finite_of_univ (j : ℕ)
    [Module.Finite (MonoidAlgebra ℤ G) (CWEquivariant.wholeRep (G:=G) (X:=X) j).ρ.asModule] :
    Module.Finite (MonoidAlgebra ℤ G) (rep (G:=G) (X:=X) j).ρ.asModule :=
  Module.Finite.of_surjective (moduleMap (fromUniv j)) (val_surjective j)

lemma univ_homology_zero (j : ℕ)
    (hz : CategoryTheory.Limits.IsZero ((SingularChains.chains X).homology j)) :
    CategoryTheory.Limits.IsZero ((SingularChains.chains (univ : Set X)).homology j) := by
  have hinj : Function.Injective (homologyMap (SingularChains.map (val (X:=X))) j) := by
    intro x y h
    have he : (ofVal (X:=X)).comp val = ContinuousMap.id _ := by ext x; rfl
    have hr : homologyMap (SingularChains.map (val (X:=X))) j ≫
      homologyMap (SingularChains.map ofVal) j = 𝟙 _ := by
      rw [← homologyMap_comp,← SingularChains.map_comp,he,SingularChains.map_id,homologyMap_id]
    have hh := congrArg (fun z => homologyMap (SingularChains.map (ofVal (X:=X))) j z) h
    change (homologyMap (SingularChains.map val) j ≫ homologyMap (SingularChains.map ofVal) j) x =
      (homologyMap (SingularChains.map val) j ≫ homologyMap (SingularChains.map ofVal) j) y at hh
    simpa only [hr,ConcreteCategory.id_apply] using hh
  let := ModuleCat.isZero_iff_subsingleton.mp hz
  let := hinj.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

attribute [instance] AddCommGroup.toIntModule
end SingularAction

namespace CoveringCellGeometry
open Set Topology unitInterval
variable {X E A : Type*} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace A] {p : E → X} (cov : IsCoveringMap p)
variable (d : E ≃ₜ E) (hd : p ∘ d = p)

def deckPullback (f : C(A,X)) (z : Pullback (p := p) f) : Pullback (p := p) f :=
  ⟨(z.1.1,d z.1.2),(congrFun hd z.1.2).trans z.2⟩

theorem familyLift_deck (H : C(I × A,X)) (z : Pullback (p := p) (endpoint H 0)) (t : I) :
    familyLift cov H (t,deckPullback d hd (endpoint H 0) z) = d (familyLift cov H (t,z)) := by
  have he : (fun t : I => familyLift cov H (t,deckPullback d hd (endpoint H 0) z)) =
      (fun t : I => d (familyLift cov H (t,z))) := by
    apply cov.eq_of_comp_eq
      ((familyLift cov H).continuous.comp (continuous_id.prodMk continuous_const))
      (d.continuous.comp ((familyLift cov H).continuous.comp
        (continuous_id.prodMk continuous_const))) ?_ 0 ?_
    · funext t
      exact (familyLift_proj cov H t _).trans
        ((congrFun hd (familyLift cov H (t,z))).trans (familyLift_proj cov H t z)).symm
    · change familyLift cov H (0,deckPullback d hd (endpoint H 0) z) = d (familyLift cov H (0,z))
      rw [familyLift_zero,familyLift_zero]
      rfl
  exact congrFun he t

variable [ContractibleSpace A] (f : C(A,X))

theorem characteristicLift_deck (j : p ⁻¹' {f (contractionPoint A)}) (a : A) :
    characteristicLift cov f ⟨d j,(congrFun hd j).trans j.2⟩ a =
      d (characteristicLift cov f j a) := by
  let H := contractionImage f
  let z : Pullback (p := p) (endpoint H 0) :=
    pullbackCongr (contractionImage_zero f).symm (constantPullback (p := p) _ (a,j))
  have hpoint : z.1 = (a,(j : E)) := by
    simp only [z,pullbackCongr_val]
    rfl
  have hpoint' : (pullbackCongr (contractionImage_zero f).symm
      (constantPullback (p := p) (f (contractionPoint A))
        (a,⟨d j,(congrFun hd j).trans j.2⟩))) = deckPullback d hd (endpoint H 0) z := by
    apply Subtype.ext
    simp only [pullbackCongr_val,deckPullback,hpoint]
    rfl
  change (pullbackCongr (contractionImage_one f)
    (transportHomeomorph cov H
      (pullbackCongr (contractionImage_zero f).symm
        (constantPullback (p := p) (f (contractionPoint A))
          (a,⟨d j,(congrFun hd j).trans j.2⟩))))).1.2 =
    d ((pullbackCongr (contractionImage_one f)
      (transportHomeomorph cov H z)).1.2)
  simp only [pullbackCongr_val,hpoint']
  exact familyLift_deck cov d hd H z 1

end CoveringCellGeometry

namespace EquivariantCoverCells
open Set Topology CategoryTheory
open CoveringCW
open scoped MonoidAlgebra
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
    [T2Space X] [T2Space E] [CWComplex (univ : Set X)]
    {G : Type u} [Group G] [MulAction G E] [ContinuousConstSMul G E]
    {p : E → X} [hproj : Fact (∀ (g : G) x, p (g • x) = p x)]
    (hfree : ∀ (g h : G) (x : E), g • x = h • x → g = h)
    (htrans : ∀ (a b : E), p a = p b → ∃ g : G, g • a = b)
    (surj : Function.Surjective p)

instance cellAction (n : ℕ) : MulAction G (Cell (p := p) n) where
  smul d c := ⟨c.1,⟨d • c.2.1,(hproj.out d c.2.1).trans c.2.2⟩⟩
  one_smul c := by
    rcases c with ⟨i,c⟩
    change (⟨i,⟨(1:G) • c.1,_⟩⟩ : Cell (p:=p) n) = ⟨i,c⟩
    exact congrArg (Sigma.mk i) (Subtype.ext (one_smul G c.1))
  mul_smul d e c := by
    change (⟨c.1,⟨(d*e) • c.2.1,_⟩⟩ : Cell (p:=p) n) = ⟨c.1,⟨d • (e • c.2.1),_⟩⟩
    exact congrArg (Sigma.mk c.1) (Subtype.ext (mul_smul d e c.2.1))

noncomputable def seed (n : ℕ) (i : BaseCell (X := X) n) : Fiber (p := p) n i :=
  ⟨Classical.choose (surj (baseChar n i (CoveringCellGeometry.contractionPoint (Disk n)))),
    Classical.choose_spec (surj (baseChar n i (CoveringCellGeometry.contractionPoint (Disk n))))⟩

noncomputable def cellEquiv (n : ℕ) : BaseCell (X := X) n × G ≃ Cell (p := p) n :=
  Equiv.ofBijective (fun z => z.2 • (⟨z.1,seed surj n z.1⟩ : Cell (p := p) n)) (by
    constructor
    · rintro ⟨i,d⟩ ⟨j,e⟩ h
      have hij : i = j := congrArg Sigma.fst h
      subst j
      have hde : d = e := hfree d e (seed surj n i).1
        (congrArg (fun c : Cell (p := p) n => (c.2 : E)) h)
      exact Prod.ext rfl hde
    · rintro ⟨i,a⟩
      obtain ⟨d,hd⟩ := htrans (seed surj n i) a ((seed surj n i).2.trans a.2.symm)
      refine ⟨(i,d),?_⟩
      change (⟨i, ⟨d • (seed surj n i).1, _⟩⟩ : Cell (p := p) n) = ⟨i,a⟩
      exact congrArg (Sigma.mk i) (Subtype.ext hd))

omit [TopologicalSpace E] [T2Space X] [T2Space E] [ContinuousConstSMul G E] in
@[simp] theorem cellEquiv_smul (n : ℕ) (d g : G) (i : BaseCell (X := X) n) :
    cellEquiv hfree htrans surj n (i,d*g) = d • cellEquiv hfree htrans surj n (i,g) := by
  change ((d*g) • (⟨i,seed surj n i⟩ : Cell (p := p) n)) = _
  exact mul_smul d g _

noncomputable abbrev cellularRepresentation (n : ℕ) :=
  Representation.ofMulAction ℤ G (Cell (p := p) n)

noncomputable def abelianEquiv (n : ℕ) :
    (BaseCell (X := X) n →₀ MonoidAlgebra ℤ G) ≃ₗ[ℤ]
      MonoidAlgebra ℤ (Cell (p := p) n) :=
  ((Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ)).trans
    ((Finsupp.curryLinearEquiv ℤ).symm.trans
      (Finsupp.domLCongr (cellEquiv hfree htrans surj n)))).trans
    (MonoidAlgebra.coeffLinearEquiv ℤ).symm

omit [TopologicalSpace E] [T2Space X] [T2Space E] [ContinuousConstSMul G E] in
@[simp] theorem abelianEquiv_single (n : ℕ) (i : BaseCell (X := X) n)
    (d : G) (a : ℤ) :
    abelianEquiv hfree htrans surj n (Finsupp.single i (MonoidAlgebra.single d a)) =
      MonoidAlgebra.single (cellEquiv hfree htrans surj n (i,d)) a := by
  simp [abelianEquiv, Finsupp.curryLinearEquiv]

noncomputable def representationEquiv (n : ℕ) :
    (Representation.free ℤ G (BaseCell (X := X) n)).Equiv
      (cellularRepresentation (p:=p) (G:=G) n) :=
  Representation.Equiv.mk (abelianEquiv hfree htrans surj n) (by
    intro d
    apply Finsupp.lhom_ext'
    intro i
    apply MonoidAlgebra.lhom_ext'
    intro g
    ext a
    simp only [LinearMap.comp_apply,Finsupp.lsingle_apply,MonoidAlgebra.lsingle_apply,LinearEquiv.coe_coe,Representation.free_single_single,
      abelianEquiv_single,Representation.ofMulAction_single,cellEquiv_smul])

noncomputable def freeIso (n : ℕ) : Rep.of (cellularRepresentation (p:=p) (G:=G) n) ≅
    Rep.free ℤ G (BaseCell (X:=X) n) :=
  (Rep.mkIso (representationEquiv hfree htrans surj n)).symm

noncomputable def freeEquiv (n : ℕ) :
    (BaseCell (X := X) n →₀ MonoidAlgebra ℤ G) ≃ₗ[MonoidAlgebra ℤ G]
      (cellularRepresentation (p:=p) (G:=G) n).asModule :=
  (Representation.finsuppLEquivFreeAsModule ℤ G (BaseCell (X := X) n)).trans
    (LinearEquiv.ofBijective
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (representationEquiv hfree htrans surj n).toIntertwiningMap)
      (representationEquiv hfree htrans surj n).toLinearEquiv.bijective)

noncomputable def basis (n : ℕ) :
    Module.Basis (BaseCell (X := X) n) (MonoidAlgebra ℤ G)
      (cellularRepresentation (p:=p) (G:=G) n).asModule :=
  (Finsupp.basisSingleOne).map (freeEquiv hfree htrans surj n)

include hfree htrans surj in
omit [TopologicalSpace E] [T2Space X] [T2Space E] [ContinuousConstSMul G E] in
theorem free (n : ℕ) : Module.Free (MonoidAlgebra ℤ G)
    (cellularRepresentation (p:=p) (G:=G) n).asModule :=
  Module.Free.of_basis (basis hfree htrans surj n)

include hfree htrans surj in
omit [TopologicalSpace E] [T2Space X] [T2Space E] [ContinuousConstSMul G E] in
theorem finite [CWComplex.FiniteType (univ : Set X)] (n : ℕ) :
    Module.Finite (MonoidAlgebra ℤ G)
      (cellularRepresentation (p:=p) (G:=G) n).asModule :=
by
  let : Finite (BaseCell (X := X) n) := RelCWComplex.FiniteType.finite_cell n
  exact Module.Finite.of_basis (basis hfree htrans surj n)

def actionHomeo (g : G) : E ≃ₜ E where
  toFun := (g • ·)
  invFun := (g⁻¹ • ·)
  left_inv x := inv_smul_smul g x
  right_inv x := smul_inv_smul g x
  continuous_toFun := continuous_const_smul g
  continuous_invFun := continuous_const_smul g⁻¹

omit [T2Space X] [T2Space E] in
lemma chart_smul (cov : IsCoveringMap p) (g : G) (n : ℕ)
    (c : Cell (p:=p) n) (v : Disk n) :
    g • chart cov n c v = chart cov n (g • c) v := by
  change g • characteristic cov n c v = characteristic cov n (g • c) v
  rw [characteristic_on_disk,characteristic_on_disk]
  exact (CoveringCellGeometry.characteristicLift_deck cov (actionHomeo g)
    (funext (hproj.out g)) (baseChar n c.1) c.2 v).symm

end EquivariantCoverCells

end

namespace EquivariantCoverCells
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CategoryTheory CWEquivariant CWExtension CoveringCW
variable {X E G : Type} [TopologicalSpace X] [TopologicalSpace E]
  [T2Space X] [T2Space E] [CWComplex (univ : Set X)]
  [Group G] [MulAction G E] [ContinuousConstSMul G E]
  {p : E → X} [hproj : Fact (∀ (g : G) x, p (g • x) = p x)]
  (hfree : ∀ (g h : G) (x : E), g • x = h • x → g = h)
  (htrans : ∀ (a b : E), p a = p b → ∃ g : G, g • a = b)
  (surj : Function.Surjective p) (cov : IsCoveringMap p)

include hfree htrans surj cov in

lemma homology_finite [PathConnectedSpace (univ : Set E)]
    (n : ℕ) [Finite (RelCWComplex.cell (univ : Set X) (n+1))]
    (hex : ∀ j, 0 < j → j < n+1 →
      CategoryTheory.Limits.IsZero ((SingularChains.chains (univ : Set E)).homology j))
    (hzero : ∀ I : Type, CategoryTheory.Limits.IsZero
      (groupHomology (RegularProductR.rep ℤ G I) (n+1))) :
    Module.Finite (MonoidAlgebra ℤ G) (wholeRep (G:=G) (X:=E) (n+1)).ρ.asModule := by
  let := CoveringCW.cwComplex_general cov
  let : ∀ m, MulAction G (RelCWComplex.cell (univ : Set E) m) := fun m => cellAction (p:=p) m
  have hc : ∀ (g : G) m (i : RelCWComplex.cell (univ : Set E) m) (v : CWExtension.Disk m),
      g • RelCWComplex.map m i v = RelCWComplex.map m (g • i) v := chart_smul cov
  have e (m : ℕ) : object (G:=G) (X:=E) m ≅ Rep.free ℤ G (RelCWComplex.cell (univ : Set X) m) :=
    freeIso hfree htrans surj m
  let : ∀ m, Projective (object (G:=G) (X:=E) m) := fun m =>
    Projective.of_iso (e m).symm inferInstance
  exact CWEquivariant.homology_finite hc n (e (n+1)) (e n) hex hzero

attribute [instance] AddCommGroup.toIntModule
end EquivariantCoverCells

end

end OAI

import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonPlacementAlternating

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TransitiveInduction

open Classical CategoryTheory Representation Finsupp
namespace TransitiveInduction
variable {G X : Type} [Group G] [MulAction G X] (x : X)

noncomputable def permutationRep : Representation ℤ G (X →₀ ℤ) where
  toFun g := Finsupp.lmapDomain ℤ ℤ (g • ·)
  map_one' := by ext y z; simp
  map_mul' g h := by ext y z; simp [mul_smul]

@[simp] lemma permutationRep_single (g : G) (y : X) (z : ℤ) :
    permutationRep (G:=G) (X:=X) g (Finsupp.single y z)=Finsupp.single (g • y) z := by
  simp [permutationRep]

noncomputable def pointMap : Rep.trivial ℤ (MulAction.stabilizer G x) ℤ ⟶
    Rep.res (MulAction.stabilizer G x).subtype (Rep.of (permutationRep (G:=G) (X:=X))) :=
  Rep.ofHom ⟨Finsupp.lsingle x,by
    intro g
    apply LinearMap.ext
    intro z
    change Finsupp.single x z=permutationRep (G:=G) (X:=X) g.val (Finsupp.single x z)
    rw [permutationRep_single]
    exact congrArg (fun y => Finsupp.single y z) g.property.symm⟩

noncomputable def toPermutation :
    Rep.ind (MulAction.stabilizer G x).subtype (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) ⟶
      Rep.of (permutationRep (G:=G) (X:=X)) :=
  (Rep.indResHomEquiv _ _ _).symm (pointMap (G:=G) x)

@[simp] theorem toPermutation_mk (g : G) (z : ℤ) :
    toPermutation (G:=G) x (IndV.mk (MulAction.stabilizer G x).subtype
      (Representation.trivial ℤ (MulAction.stabilizer G x) ℤ) g z)=Finsupp.single (g⁻¹ • x) z := by
  simp [toPermutation,Rep.indResHomEquiv,pointMap]

lemma mk_same {g h : G} (he : g⁻¹ • x=h⁻¹ • x) (z : ℤ) :
    IndV.mk (MulAction.stabilizer G x).subtype
      (Representation.trivial ℤ (MulAction.stabilizer G x) ℤ) g z=
    IndV.mk (MulAction.stabilizer G x).subtype
      (Representation.trivial ℤ (MulAction.stabilizer G x) ℤ) h z := by
  have hs : h*g⁻¹∈MulAction.stabilizer G x := by
    change (h*g⁻¹) • x=x
    rw [mul_smul,he,smul_inv_smul]
  have hh := Coinvariants.mk_self_apply
    (Representation.tprod ((Representation.leftRegular ℤ G).comp (MulAction.stabilizer G x).subtype)
      (Representation.trivial ℤ (MulAction.stabilizer G x) ℤ))
    (⟨h*g⁻¹,hs⟩ : MulAction.stabilizer G x)
    (TensorProduct.tmul ℤ (MonoidAlgebra.single g (1:ℤ)) z)
  simpa [IndV.mk,Representation.tprod_apply,mul_assoc] using hh.symm

noncomputable def transport (ht : ∀y : X,∃g : G,g • x=y) (y : X) : G := (ht y).choose
@[simp] theorem transport_spec (ht : ∀y : X,∃g : G,g • x=y) (y : X) :
    transport x ht y • x=y := (ht y).choose_spec

noncomputable def fromPermutation (ht : ∀y : X,∃g : G,g • x=y) :
    (X →₀ ℤ) →ₗ[ℤ] Representation.IndV (MulAction.stabilizer G x).subtype
      (Representation.trivial ℤ (MulAction.stabilizer G x) ℤ) :=
  Finsupp.lsum ℤ (fun y => IndV.mk _ _ (transport x ht y)⁻¹)

@[simp] theorem fromPermutation_single (ht : ∀y : X,∃g : G,g • x=y) (y : X) (z : ℤ) :
    fromPermutation x ht (Finsupp.single y z)=IndV.mk _ _ (transport x ht y)⁻¹ z := by
  exact Finsupp.lsum_single ℤ _ y z

lemma from_to (ht : ∀y : X,∃g : G,g • x=y) :
    (fromPermutation x ht).comp (toPermutation (G:=G) x).hom.toLinearMap=LinearMap.id := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro z
  change fromPermutation x ht (toPermutation (G:=G) x (IndV.mk _ _ g z))=IndV.mk _ _ g z
  rw [toPermutation_mk,fromPermutation_single]
  apply mk_same
  simp

lemma to_from (ht : ∀y : X,∃g : G,g • x=y) :
    (toPermutation (G:=G) x).hom.toLinearMap.comp (fromPermutation x ht)=LinearMap.id := by
  apply Finsupp.lhom_ext
  intro y z
  change toPermutation (G:=G) x (fromPermutation x ht (Finsupp.single y z))=Finsupp.single y z
  rw [fromPermutation_single,toPermutation_mk]
  simp

noncomputable def iso (ht : ∀y : X,∃g : G,g • x=y) :
    Rep.ind (MulAction.stabilizer G x).subtype (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) ≅
      Rep.of (permutationRep (G:=G) (X:=X)) :=
  Rep.mkIso (Representation.IntertwiningMap.ofBijective (toPermutation (G:=G) x).hom
    ⟨by
      intro u v he
      exact (LinearMap.congr_fun (from_to x ht) u).symm.trans
        ((congrArg (fromPermutation x ht) he).trans (LinearMap.congr_fun (from_to x ht) v)),
      fun y => ⟨fromPermutation x ht y,LinearMap.congr_fun (to_from x ht) y⟩⟩)

noncomputable def homologyIso (ht : ∀y : X,∃g : G,g • x=y) (q : ℕ) :
    groupHomology (Rep.of (permutationRep (G:=G) (X:=X))) q ≅
      groupHomology (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) q :=
  (groupHomology.functor ℤ G q).mapIso (iso x ht).symm ≪≫ groupHomology.indIso _ _ q

end TransitiveInduction
end TransitiveInduction

section PolygonConfigurationModule

open Classical CategoryTheory Finsupp
namespace PolygonPlacement.Configuration
variable {a m p : ℕ}

noncomputable def listEquiv (a m p : ℕ) : Configuration a m p ≃
    {l : List (PolygonPlacement a m) // l.Pairwise Apart ∧ l.length=p} where
  toFun f := ⟨List.ofFn f.val,List.pairwise_ofFn.mpr (fun _ _ h => f.property (ne_of_lt h)),List.length_ofFn⟩
  invFun l := ⟨fun i => l.val.get ⟨i.val,by rw [l.property.2];exact i.isLt⟩,by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h|h
    · exact l.property.1.rel_get_of_lt h
    · exact (l.property.1.rel_get_of_lt h).symm⟩
  left_inv f := by apply ext; intro i; simp
  right_inv l := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp [l.property.2]
    · intro i hi hj
      simp

@[simp] theorem listEquiv_apply_val (f : Configuration a m p) :
    (listEquiv a m p f).val=List.ofFn f.val := rfl

noncomputable def chainEquiv (a m p : ℕ) :
    (Configuration a m p →₀ ℤ) ≃ₗ[ℤ] ConfigurationChains.degree (@Apart a m) p :=
  (Finsupp.domLCongr (listEquiv a m p)).trans (ConfigurationChains.simplexModuleEquiv _ p).symm

@[simp] theorem chainEquiv_single_val (f : Configuration a m p) (z : ℤ) :
    (chainEquiv a m p (Finsupp.single f z)).val=Finsupp.single (List.ofFn f.val) z := by
  unfold chainEquiv
  rw [LinearEquiv.trans_apply,Finsupp.domLCongr_single]
  simp [ConfigurationChains.simplexModuleEquiv]
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

theorem chainEquiv_intertwines (g : polygonFullGroup a m) :
    (chainEquiv a m p).toLinearMap.comp (TransitiveInduction.permutationRep
      (G:=polygonFullGroup a m) (X:=Configuration a m p) g)=
    (configurationRepresentation a m p g).comp (chainEquiv a m p).toLinearMap := by
  apply Finsupp.lhom_ext
  intro f z
  apply Subtype.ext
  change (chainEquiv a m p (TransitiveInduction.permutationRep g (Finsupp.single f z))).val=
    ConfigurationChains.push (fun v => g • v) (chainEquiv a m p (Finsupp.single f z)).val
  rw [TransitiveInduction.permutationRep_single,chainEquiv_single_val,chainEquiv_single_val,
    ConfigurationChains.push_single]
  congr 1
  simp [List.map_ofFn]
  rfl

noncomputable def representationIso (a m p : ℕ) :
    Rep.of (TransitiveInduction.permutationRep (G:=polygonFullGroup a m) (X:=Configuration a m p)) ≅
      Rep.of (configurationRepresentation a m p) :=
  Rep.mkIso {toLinearEquiv:=chainEquiv a m p,isIntertwining':=chainEquiv_intertwines}

noncomputable def columnHomologyIso (a p n : ℕ) (hm : 3*p+1 < p+n) (q : ℕ) :
    groupHomology (Rep.of (configurationRepresentation a (p+n) p)) q ≅
      groupHomology (Rep.trivial ℤ (MulAction.stabilizer (polygonFullGroup a (p+n))
        (standard a p n)) ℤ) q :=
  (groupHomology.functor ℤ _ q).mapIso (representationIso a (p+n) p).symm ≪≫
    TransitiveInduction.homologyIso (standard a p n) (fun f => transitive _ f hm) q

end PolygonPlacement.Configuration
end PolygonConfigurationModule

end SimpleAmenable
end
end

end OAI

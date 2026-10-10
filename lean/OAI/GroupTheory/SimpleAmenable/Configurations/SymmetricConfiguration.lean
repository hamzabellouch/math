import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.HomologyAdditive

namespace OAI

section
open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2
abbrev G (m:ℕ) := Equiv.Perm (Fin m)
def Configuration (m p:ℕ) := {f:Fin p → Fin m // Function.Injective f}
variable {m p:ℕ}
instance : CoeFun (Configuration m p) (fun _=>Fin p → Fin m) := ⟨Subtype.val⟩
@[ext] theorem ext {f g:Configuration m p} (h:∀i,f i=g i) : f=g := Subtype.ext (funext h)
noncomputable instance : MulAction (G m) (Configuration m p) where
  smul g f := ⟨fun i=>g (f i), g.injective.comp f.property⟩
  one_smul f := by apply ext; intro i; rfl
  mul_smul g h f := by apply ext; intro i; rfl
@[simp] theorem smul_apply (g:G m) (f:Configuration m p) (i:Fin p) : (g • f) i=g (f i) := rfl
noncomputable def standard (p n:ℕ) : Configuration (p+n) p := ⟨Fin.castAdd n,Fin.castAdd_injective p n⟩
noncomputable def standardLE (m p:ℕ) (hp:p ≤ m) : Configuration m p := ⟨Fin.castLE hp,Fin.castLE_injective hp⟩
theorem transitive (f g:Configuration m p) : ∃u:G m,u • f=g := by
  obtain ⟨u,hu⟩ := Equiv.Perm.exists_extending_pair f.val g.val f.property g.property
  exact ⟨u,ext hu⟩
lemma ne_smul (g:G m) (v w:Fin m) (h:v ≠ w) : g • v ≠ g • w := fun hh=>h (g.injective hh)
noncomputable def configurationRepresentation (m p:ℕ) : Representation ℤ (G m) (ConfigurationChains.degree (Ne:Fin m → Fin m → Prop) p) :=
  ConfigurationChains.representation ne_smul p
lemma commonNeighbor (hm:32 ≤ m) (S:Finset (Fin m)) (hS:S.card ≤ 31) : ∃v,∀w ∈ S,v ≠ w := by
  obtain ⟨v,hv⟩ := Finset.exists_mem_notMem_of_card_lt_card (s:=S) (t:=Finset.univ) (by simpa using (show S.card < m by omega))
  exact ⟨v,by intro w hw he; exact hv.2 (he ▸ hw)⟩
lemma lowDegree_exact (hm:32 ≤ m) {n:ℕ} (hn:n ≤ 2) :
    Function.Exact (ConfigurationChains.degreeBoundary (Ne:Fin m → Fin m → Prop) (n+1))
      (ConfigurationChains.degreeBoundary (Ne:Fin m → Fin m → Prop) n) :=
  ConfigurationChains.lowDegree_exact (commonNeighbor hm) hn
noncomputable def listEquiv (m p : ℕ) : Configuration m p ≃
    {l : List (Fin m) // l.Pairwise Ne ∧ l.length=p} where
  toFun f := ⟨List.ofFn f.val,List.pairwise_ofFn.mpr (fun _ _ h => fun hh => (ne_of_lt h) (f.property hh)),List.length_ofFn⟩
  invFun l := ⟨fun i => l.val.get ⟨i.val,by rw [l.property.2];exact i.isLt⟩,by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h|h
    · exact l.property.1.rel_get_of_lt h hij
    · exact l.property.1.rel_get_of_lt h hij.symm⟩
  left_inv f := by apply ext; intro i; simp
  right_inv l := by
    apply Subtype.ext
    apply List.ext_getElem
    · simp [l.property.2]
    · intro i hi hj
      simp

@[simp] theorem listEquiv_apply_val (f : Configuration m p) :
    (listEquiv m p f).val=List.ofFn f.val := rfl

noncomputable def chainEquiv (m p : ℕ) :
    (Configuration m p  →₀ ℤ) ≃ₗ[ℤ] ConfigurationChains.degree ((Ne:Fin m → Fin m → Prop)) p :=
  (Finsupp.domLCongr (listEquiv m p)).trans (ConfigurationChains.simplexModuleEquiv _ p).symm

@[simp] theorem chainEquiv_single_val (f : Configuration m p) (z : ℤ) :
    (chainEquiv m p (Finsupp.single f z)).val=Finsupp.single (List.ofFn f.val) z := by
  unfold chainEquiv
  rw [LinearEquiv.trans_apply,Finsupp.domLCongr_single]
  simp [ConfigurationChains.simplexModuleEquiv]
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

theorem chainEquiv_intertwines (g : G m) :
    (chainEquiv m p).toLinearMap.comp (TransitiveInduction.permutationRep
      (G:=G m) (X:=Configuration m p) g)=
    (configurationRepresentation m p g).comp (chainEquiv m p).toLinearMap := by
  apply Finsupp.lhom_ext
  intro f z
  apply Subtype.ext
  change (chainEquiv m p (TransitiveInduction.permutationRep g (Finsupp.single f z))).val=
    ConfigurationChains.push (fun v => g  •  v) (chainEquiv m p (Finsupp.single f z)).val
  rw [TransitiveInduction.permutationRep_single,chainEquiv_single_val,chainEquiv_single_val,
    ConfigurationChains.push_single]
  congr 1
  simp [List.map_ofFn]
  rfl

noncomputable def representationIso (m p : ℕ) :
    Rep.of (TransitiveInduction.permutationRep (G:=G m) (X:=Configuration m p)) ≅
      Rep.of (configurationRepresentation m p) :=
  Rep.mkIso {toLinearEquiv:=chainEquiv m p,isIntertwining':=chainEquiv_intertwines}

noncomputable abbrev column (m p : ℕ) :=
  Rep.of (TransitiveInduction.permutationRep
    (G:=G m) (X:=Configuration m p))

noncomputable def face (i : Fin (p+1)) (f : Configuration m (p+1)) :
    Configuration m p :=
  ⟨fun j => f (i.succAbove j),f.property.comp Fin.succAbove_right_injective⟩

@[simp] lemma face_apply (i : Fin (p+1)) (f : Configuration m (p+1)) (j : Fin p) :
    face i f j=f (i.succAbove j) := rfl

@[simp] lemma face_smul (i : Fin (p+1)) (g : G m)
    (f : Configuration m (p+1)) : face i (g  •  f)=g  •  face i f := rfl

noncomputable def faceHom (m p : ℕ) (i : Fin (p+1)) :
    column m (p+1) ⟶ column m p :=
  TransitiveInduction.equivariantMap (face i) (face_smul i)

noncomputable def boundary (m p : ℕ) : column m (p+1) ⟶ column m p :=
  (representationIso m (p+1)).hom ≫
    ConfigurationChains.boundaryRep ne_smul p ≫
    (representationIso m p).inv

lemma boundary_chain (c : Configuration m (p+1)  →₀ ℤ) :
    chainEquiv m p ((boundary m p).hom c) =
      ConfigurationChains.degreeBoundary ((Ne:Fin m → Fin m → Prop)) p (chainEquiv m (p+1) c) := by
  change chainEquiv m p ((chainEquiv m p).symm _) = _
  exact (chainEquiv m p).apply_symm_apply _

lemma boundary_sum (m p : ℕ) : boundary m p =
    ∑i : Fin (p+1), ((-1:ℤ)^i.val)  •  faceHom m p i := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply Finsupp.lhom_ext
  intro c z
  apply (chainEquiv m p).injective
  change (chainEquiv m p) ((boundary m p).hom (Finsupp.single c z)) = _
  rw [boundary_chain]
  apply Subtype.ext
  change ConfigurationChains.boundary (chainEquiv m (p+1) (Finsupp.single c z)).val = _
  rw [chainEquiv_single_val, ConfigurationChains.boundary_single,
    ConfigurationChains.faceSum_ofFn]
  simp only [Finset.smul_sum]
  change _ = (chainEquiv m p
    ((∑i : Fin (p+1), ((-1:ℤ)^i.val)  •  faceHom m p i).hom (Finsupp.single c z))).val
  simp only [Rep.sum_hom, Rep.smul_hom, Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.smul_apply, map_sum, map_smul, Submodule.coe_sum,
    Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro i hi
  change z  •  Finsupp.single _ ((-1:ℤ)^i.val) =
    ((-1:ℤ)^i.val)  •  ((chainEquiv m p)
      ((faceHom m p i).hom (Finsupp.single c z))).val
  dsimp only [faceHom]
  rw [TransitiveInduction.equivariantMap_single]
  rw [chainEquiv_single_val]
  simp [Finsupp.smul_single, mul_comm, face]

end SimpleAmenable.SymmetricConfiguration

end

end OAI

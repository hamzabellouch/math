import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonTrackStabilizer
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonPlacementPermutation

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonPlacementAlternating

open Classical Set
namespace PolygonPlacement
variable {a m n : ℕ}

theorem permHom_mem_alternating (f : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j))) (hm : 3*n+1 < m)
    {σ : Equiv.Perm (Fin n)} (hσ : σ∈alternatingGroup (Fin n)) :
    permHom f hf σ∈polygonAlternatingGroup a m := by
  let ι : Fin n ↪ Fin m := Fin.castLEEmb (by omega)
  let s : Fin n → PolygonPlacement a m := fun i => standard (ι i)
  have hs : Pairwise (fun i j => Apart (s i) (s j)) :=
    fun _ _ hij => standard_apart (ι.injective.ne hij)
  obtain ⟨g,hg⟩ := configuration_transitive s f hs hf hm
  have hgs (i : Fin n) (x : GenericSquare a) : g.val (ι i,x)=f i x :=
    congrArg (fun e : PolygonPlacement a m => e x) (hg i)
  let slots : Fin n → Fin m × (CutRing×CutRing) := fun i => (ι i,0)
  have hinj : Function.Injective (SlotMap a m ⊤ slots) :=
    slots_injective_of_tracks ⊤ slots ι.injective
  have hslot (i : Fin n) (x : (⊤ : polygonAlgebra a).val) :
      SlotMap a m ⊤ slots (i,x)=(ι i,x.val) := by
    change (ι i,translate a 0 x.val)=(ι i,x.val)
    rw [translate_zero]
  have he : g*slotHom ⊤ slots hinj σ*g⁻¹=permHom f hf σ := by
    apply Subtype.ext; apply Equiv.ext
    intro p
    obtain ⟨q,rfl⟩ := g.val.surjective p
    change g.val (slotPerm ⊤ slots hinj σ (g.val.symm (g.val q)))=perm f hf σ (g.val q)
    rw [g.val.symm_apply_apply]
    by_cases hq : q∈Set.range (SlotMap a m ⊤ slots)
    · obtain ⟨⟨i,x⟩,rfl⟩ := hq
      rw [slotPerm_apply,hslot,hslot,hgs,hgs,perm_apply]
    · rw [slotPerm_apply_of_notMem _ _ _ _ hq]
      symm
      apply perm_fixed
      intro i hmem
      obtain ⟨x,hx⟩ := hmem
      have hp : q=(ι i,x) := g.val.injective (hx.symm.trans (hgs i x).symm)
      exact hq ⟨(i,⟨x,by trivial⟩),(hslot i ⟨x,by trivial⟩).trans hp.symm⟩
  rw [←he]
  exact (polygonAlternatingGroup_normal a m).conj_mem _ (slotHom_alternating_mem _ _ _ hσ) g

end PolygonPlacement
end PolygonPlacementAlternating

section PolygonAlternatingTransitive

open Classical Set
namespace PolygonPlacement
variable {a m n : ℕ}

theorem familyPerm_mem_alternating {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → PolygonPlacement a m) (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hm : 3*Fintype.card ι+1 < m) {σ : Equiv.Perm ι}
    (hσ : σ∈alternatingGroup ι) : familyPerm f hf σ∈polygonAlternatingGroup a m := by
  apply permHom_mem_alternating _ _ hm
  change Equiv.Perm.sign (((Fintype.equivFin ι).symm.trans σ).trans (Fintype.equivFin ι))=1
  rw [Equiv.Perm.sign_symm_trans_trans]
  exact hσ

theorem alternating_move_to_bank (f : Fin n → PolygonPlacement a m)
    (w : Fin (n+2) → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hw : Pairwise (fun i j => Apart (w i) (w j)))
    (hfw : ∀i j,Apart (f i) (w j)) (hm : 6*n+7 < m) :
    ∃h : polygonAlternatingGroup a m,∀i x,h.val.val (f i x)=w (i.castAdd 2) x := by
  let e : Fin n ⊕ Fin (n+2) → PolygonPlacement a m := Sum.elim f w
  have he : Pairwise (fun i j => Apart (e i) (e j)) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hf (fun hh => hij (congrArg Sum.inl hh))
      | inr j => exact hfw i j
    | inr i =>
      cases j with
      | inl j => exact (hfw j i).symm
      | inr j => exact hw (fun hh => hij (congrArg Sum.inr hh))
  let s : Fin n ↪ Fin n ⊕ Fin (n+2) := ⟨Sum.inl,Sum.inl_injective⟩
  let t : Fin n ↪ Fin n ⊕ Fin (n+2) :=
    ⟨fun i => Sum.inr (i.castAdd 2),by
      intro i j h
      have hc : i.castAdd 2=j.castAdd 2 := Sum.inr_injective h
      have hv := congrArg (fun x : Fin (n+2) => x.val) hc
      exact Fin.ext hv⟩
  obtain ⟨σ,hσ⟩ := even_move_embedding (s:=s) (t:=t) (by simp [Nat.card_eq_fintype_card])
  have hb : 3*Fintype.card (Fin n ⊕ Fin (n+2))+1 < m := by
    simp only [Fintype.card_sum,Fintype.card_fin]
    omega
  refine ⟨⟨familyPerm e he σ.val,familyPerm_mem_alternating e he hb σ.property⟩,?_⟩
  intro i x
  have hh := familyPerm_apply e he σ.val (s i) x
  rw [hσ] at hh
  exact hh

theorem alternating_configuration_transitive (f g : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hg : Pairwise (fun i j => Apart (g i) (g j))) (hm : 6*n+7 < m) :
    ∃h : polygonAlternatingGroup a m,∀i,h.val • f i=g i := by
  let S := Finset.univ.image f ∪ Finset.univ.image g
  have hS : S.card≤2*n := by
    calc
      _≤(Finset.univ.image f).card+(Finset.univ.image g).card := Finset.card_union_le _ _
      _≤(Finset.univ : Finset (Fin n)).card+(Finset.univ : Finset (Fin n)).card :=
        Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _=2*n := by simp; omega
  obtain ⟨w,hw,hws⟩ := exists_configuration_avoiding S (n+2) (by omega)
  have hfw (i : Fin n) (j : Fin (n+2)) : Apart (f i) (w j) :=
    (hws j (f i) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))).symm
  have hgw (i : Fin n) (j : Fin (n+2)) : Apart (g i) (w j) :=
    (hws j (g i) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))).symm
  obtain ⟨u,hu⟩ := alternating_move_to_bank f w hf hw hfw hm
  obtain ⟨v,hv⟩ := alternating_move_to_bank g w hg hw hgw hm
  refine ⟨v⁻¹*u,fun i => ?_⟩
  apply PolygonPlacement.ext
  intro x
  change v.val.val.symm (u.val.val (f i x))=g i x
  rw [hu]
  exact v.val.val.symm_apply_eq.mpr (hv i x).symm

end PolygonPlacement
end PolygonAlternatingTransitive

section PolygonConfigurationOrbit
open Classical Set
namespace PolygonPlacement

def Configuration (a m p : ℕ) :=
  {f : Fin p → PolygonPlacement a m // Pairwise (fun i j => Apart (f i) (f j))}

namespace Configuration
variable {a m p : ℕ}
instance : CoeFun (Configuration a m p) (fun _ => Fin p → PolygonPlacement a m) := ⟨Subtype.val⟩

@[ext] theorem ext {f g : Configuration a m p} (h : ∀i,f i=g i) : f=g :=
  Subtype.ext (funext h)

noncomputable instance : MulAction (polygonFullGroup a m) (Configuration a m p) where
  smul g f := ⟨fun i => g • f i,fun i j hij => (apart_smul_iff g _ _).mpr (f.property hij)⟩
  one_smul f := by apply ext; intro i; exact one_smul _ _
  mul_smul g h f := by apply ext; intro i; exact mul_smul g h _

@[simp] theorem smul_apply (g : polygonFullGroup a m) (f : Configuration a m p) (i : Fin p) :
    (g • f) i=g • f i := rfl

noncomputable def standard (a p n : ℕ) : Configuration a (p+n) p :=
  ⟨fun i => PolygonPlacement.standard (i.castAdd n),fun i j hij => standard_apart (by
    intro hh
    apply hij
    have hv := congrArg (fun x : Fin (p+n) => x.val) hh
    exact Fin.ext hv)⟩

@[simp] theorem standard_apply (i : Fin p) (x : GenericSquare a) (n : ℕ) :
    standard a p n i x=(i.castAdd n,x) := rfl

theorem stabilizer_standard (a p n : ℕ) :
    MulAction.stabilizer (polygonFullGroup a (p+n)) (standard a p n)=
      PolygonTracks.bankFixer a p n := by
  ext g
  change g • standard a p n=standard a p n ↔ _
  constructor
  · intro he x
    exact congrArg (fun f : Configuration a (p+n) p => f x.1 x.2) he
  · intro he
    apply ext
    intro i
    apply PolygonPlacement.ext
    intro x
    exact he (i,x)

theorem transitive (f g : Configuration a m p) (hm : 3*p+1 < m) :
    ∃u : polygonFullGroup a m,u • f=g := by
  obtain ⟨u,hu⟩ := configuration_transitive f.val g.val f.property g.property hm
  exact ⟨u,ext hu⟩

noncomputable def quotientStabilizerEquiv (a p n : ℕ) (hm : 3*p+1 < p+n) :
    (polygonFullGroup a (p+n) ⧸ MulAction.stabilizer (polygonFullGroup a (p+n))
      (standard a p n)) ≃ Configuration a (p+n) p :=
  Equiv.ofBijective (MulAction.ofQuotientStabilizer (polygonFullGroup a (p+n)) (standard a p n))
    ⟨MulAction.injective_ofQuotientStabilizer _ _,by
      intro f
      obtain ⟨g,hg⟩ := transitive (standard a p n) f hm
      exact ⟨g,hg⟩⟩

@[simp] theorem quotientStabilizerEquiv_apply (a p n : ℕ) (hm : 3*p+1 < p+n)
    (g : polygonFullGroup a (p+n)) :
    quotientStabilizerEquiv a p n hm g=g • standard a p n := rfl

noncomputable def quotientBankEquiv (a p n : ℕ) (hm : 3*p+1 < p+n) :
    (polygonFullGroup a (p+n) ⧸ PolygonTracks.bankFixer a p n) ≃ Configuration a (p+n) p :=
  (Subgroup.quotientEquivOfEq (stabilizer_standard a p n).symm).trans
    (quotientStabilizerEquiv a p n hm)

@[simp] theorem quotientBankEquiv_apply (a p n : ℕ) (hm : 3*p+1 < p+n)
    (g : polygonFullGroup a (p+n)) :
    quotientBankEquiv a p n hm g=g • standard a p n := rfl

theorem quotientBankEquiv_smul (a p n : ℕ) (hm : 3*p+1 < p+n)
    (g : polygonFullGroup a (p+n)) (x : polygonFullGroup a (p+n) ⧸ PolygonTracks.bankFixer a p n) :
    quotientBankEquiv a p n hm (g • x)=g • quotientBankEquiv a p n hm x := by
  induction x using Quotient.inductionOn' with
  | h h => exact mul_smul g h _

end Configuration
end PolygonPlacement
end PolygonConfigurationOrbit

end SimpleAmenable
end
end

end OAI

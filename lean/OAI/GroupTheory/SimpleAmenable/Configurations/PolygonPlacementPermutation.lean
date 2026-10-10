import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonPlacementArea

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonPlacementPermutation

open Classical Set
namespace PolygonPlacement
variable {a m n : ℕ} (f : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))

noncomputable def perm (σ : Equiv.Perm (Fin n)) : Equiv.Perm (TrackPoint a m) :=
  Equiv.Perm.viaEmbedding (Equiv.prodCongr σ (Equiv.refl _)) (bank f hf)

@[simp] theorem perm_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) (x : GenericSquare a) :
    perm f hf σ (f i x)=f (σ i) x :=
  Equiv.Perm.viaEmbedding_apply _ _ (i,x)

theorem perm_fixed (σ : Equiv.Perm (Fin n)) (p : TrackPoint a m)
    (hp : ∀i,p∉Set.range (f i)) : perm f hf σ p=p := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨⟨i,x⟩,hi⟩
  exact hp i ⟨x,hi⟩

theorem perm_hasTable (σ : Equiv.Perm (Fin n)) : HasTranslationTable (perm f hf σ) := by
  let s (i : Fin n) := (f i).charts.choose
  have hs (i : Fin n) := (f i).charts.choose_spec.1
  have hc (i : Fin n) := (f i).charts.choose_spec.2
  let J := Σi : Fin n, {c // c∈s i} × {d // d∈s (σ i)}
  let chart (j : J) : TableChart a m :=
    ⟨j.2.1.val.1,j.2.2.val.1,j.2.2.val.2.1-j.2.1.val.2.1,
      translatedPolygon j.2.1.val.2.1 (j.2.1.val.2.2 ⊓ j.2.2.val.2.2)⟩
  let V (i : Fin m) : polygonAlgebra a := (Finset.univ.sup (fun j => imageBank (f j) i))ᶜ
  have hV (p : TrackPoint a m) : p.2∈(V p.1).val ↔ ∀i,p∉Set.range (f i) := by
    simp only [V,BooleanSubalgebra.val_compl,PolygonArea.val_finset_sup,
      Set.mem_compl_iff,Set.mem_iUnion,Finset.mem_univ,not_exists,true_implies]
    rfl
  let void (i : Fin m) : TableChart a m := ⟨i,i,0,V i⟩
  refine ⟨Finset.univ.image chart ∪ Finset.univ.image void,?_,?_⟩
  · intro c hc'
    rcases Finset.mem_union.mp hc' with hc'|hc'
    · obtain ⟨j,-,rfl⟩ := Finset.mem_image.mp hc'
      intro y hy
      obtain ⟨x,⟨hx,hd⟩,rfl⟩ := hy
      have hcval := hs j.1 j.2.1.val j.2.1.property x hx
      have hdval := hs (σ j.1) j.2.2.val j.2.2.property x hd
      change perm f hf σ (j.2.1.val.1,translate a j.2.1.val.2.1 x)=
        (j.2.2.val.1,translate a (j.2.2.val.2.1-j.2.1.val.2.1) (translate a j.2.1.val.2.1 x))
      rw [←hcval,perm_apply,hdval,←translate_add,sub_add_cancel]
    · obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hc'
      intro x hx
      change perm f hf σ (i,x)=(i,translate a 0 x)
      rw [translate_zero]
      exact perm_fixed f hf σ (i,x) ((hV (i,x)).mp hx)
  · intro p
    by_cases hp : ∃i,p∈Set.range (f i)
    · obtain ⟨i,x,rfl⟩ := hp
      obtain ⟨c,hcs,hcx⟩ := hc i x
      obtain ⟨d,hds,hdx⟩ := hc (σ i) x
      let j : J := ⟨i,⟨c,hcs⟩,⟨d,hds⟩⟩
      refine ⟨chart j,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩),?_,?_⟩
      · exact congrArg Prod.fst (hs i c hcs x hcx)
      · refine ⟨x,⟨hcx,hdx⟩,?_⟩
        exact (congrArg Prod.snd (hs i c hcs x hcx)).symm
    · exact ⟨void p.1,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.1,Finset.mem_univ _,rfl⟩),
        rfl,(hV p).mpr (by simpa only [not_exists] using hp)⟩

noncomputable def permHom : Equiv.Perm (Fin n) →* polygonFullGroup a m where
  toFun σ := ⟨perm f hf σ,perm_hasTable f hf σ⟩
  map_one' := by
    apply Subtype.ext; apply Equiv.ext
    intro p
    by_cases hp : ∃i,p∈Set.range (f i)
    · obtain ⟨i,x,rfl⟩ := hp
      exact perm_apply f hf 1 i x
    · exact perm_fixed f hf 1 p (by simpa only [not_exists] using hp)
  map_mul' σ ρ := by
    apply Subtype.ext; apply Equiv.ext
    intro p
    change perm f hf (σ*ρ) p=perm f hf σ (perm f hf ρ p)
    by_cases hp : ∃i,p∈Set.range (f i)
    · obtain ⟨i,x,rfl⟩ := hp
      simp only [perm_apply,Equiv.Perm.mul_apply]
    · have h : ∀i,p∉Set.range (f i) := by simpa only [not_exists] using hp
      rw [perm_fixed f hf _ p h,perm_fixed f hf _ p h,perm_fixed f hf _ p h]

@[simp] theorem permHom_apply (σ : Equiv.Perm (Fin n)) (i : Fin n) (x : GenericSquare a) :
    (permHom f hf σ).val (f i x)=f (σ i) x := perm_apply f hf σ i x

end PolygonPlacement
end PolygonPlacementPermutation

section PolygonConfigurationTransitive

open Classical Set
namespace PolygonPlacement
variable {a m n : ℕ}

noncomputable def familyPerm {ι : Type*} [Fintype ι] (f : ι → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j))) (σ : Equiv.Perm ι) : polygonFullGroup a m :=
  let e := Fintype.equivFin ι
  permHom (fun i => f (e.symm i))
    (fun _ _ h => hf (fun he => h (e.symm.injective he)))
    (e.symm.trans (σ.trans e))

@[simp] theorem familyPerm_apply {ι : Type*} [Fintype ι] (f : ι → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j))) (σ : Equiv.Perm ι)
    (i : ι) (x : GenericSquare a) : (familyPerm f hf σ).val (f i x)=f (σ i) x := by
  let e := Fintype.equivFin ι
  have h := permHom_apply (fun j => f (e.symm j))
    (fun _ _ h => hf (fun he => h (e.symm.injective he)))
    (e.symm.trans (σ.trans e)) (e i) x
  simpa only [familyPerm,e,Equiv.symm_apply_apply,Equiv.trans_apply,Equiv.apply_symm_apply] using h

theorem exists_configuration_avoiding (S : Finset (PolygonPlacement a m)) (n : ℕ)
    (hm : S.card+n+1 < m) :
    ∃w : Fin n → PolygonPlacement a m,
      Pairwise (fun i j => Apart (w i) (w j)) ∧ ∀i f,f∈S → Apart (w i) f := by
  induction n generalizing S with
  | zero => exact ⟨Fin.elim0,by intro i; exact i.elim0,by intro i; exact i.elim0⟩
  | succ n ih =>
    obtain ⟨v,hv⟩ := common_neighbor S (by omega)
    obtain ⟨w,hw,hws⟩ := ih (insert v S) (by
      have hh := Finset.card_insert_le v S
      omega)
    refine ⟨Fin.cons v w,?_,?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact (hws j v (Finset.mem_insert_self _ _)).symm
      | succ i =>
        induction j using Fin.cases with
        | zero => exact hws i v (Finset.mem_insert_self _ _)
        | succ j => exact hw (fun he => hij (congrArg Fin.succ he))
    · intro i f hf
      induction i using Fin.cases with
      | zero => exact hv f hf
      | succ i => exact hws i f (Finset.mem_insert_of_mem hf)

theorem swap_configurations (f g : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hg : Pairwise (fun i j => Apart (g i) (g j)))
    (hfg : ∀i j,Apart (f i) (g j)) :
    ∃h : polygonFullGroup a m,∀i x,h.val (f i x)=g i x := by
  let e : Fin n ⊕ Fin n → PolygonPlacement a m := Sum.elim f g
  have he : Pairwise (fun i j => Apart (e i) (e j)) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hf (fun h => hij (congrArg Sum.inl h))
      | inr j => exact hfg i j
    | inr i =>
      cases j with
      | inl j => exact (hfg j i).symm
      | inr j => exact hg (fun h => hij (congrArg Sum.inr h))
  refine ⟨familyPerm e he (Equiv.sumComm _ _),?_⟩
  intro i x
  exact familyPerm_apply e he (Equiv.sumComm _ _) (.inl i) x

theorem configuration_transitive (f g : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hg : Pairwise (fun i j => Apart (g i) (g j))) (hm : 3*n+1 < m) :
    ∃h : polygonFullGroup a m,∀i,h • f i=g i := by
  let S := Finset.univ.image f ∪ Finset.univ.image g
  have hS : S.card≤2*n := by
    calc
      _≤(Finset.univ.image f).card+(Finset.univ.image g).card := Finset.card_union_le _ _
      _≤(Finset.univ : Finset (Fin n)).card+(Finset.univ : Finset (Fin n)).card :=
        Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _=2*n := by simp; omega
  obtain ⟨w,hw,hws⟩ := exists_configuration_avoiding S n (by omega)
  have hwf (i j : Fin n) : Apart (w i) (f j) :=
    hws i (f j) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  have hwg (i j : Fin n) : Apart (w i) (g j) :=
    hws i (g j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  obtain ⟨u,hu⟩ := swap_configurations f w hf hw (fun i j => (hwf j i).symm)
  obtain ⟨v,hv⟩ := swap_configurations w g hw hg hwg
  refine ⟨v*u,fun i => ?_⟩
  apply PolygonPlacement.ext
  intro x
  change v.val (u.val (f i x))=g i x
  rw [hu,hv]

end PolygonPlacement
end PolygonConfigurationTransitive

end SimpleAmenable
end
end

end OAI

import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalSort
import OAI.Combinatorics.KMedianRecovery.Recovery.BottomMath

namespace OAI

namespace MetricKMedianRecovery.Completion.Canonical
variable {E V : Type*} [DecidableEq E] [DecidableEq V] {a : ℕ}
def pick (part : E→Fin a) (o : Fin a→E) (xs : List E) (j : Fin a) : E :=
  ((xs.filter (fun e=>part e=j)).head?).getD (o j)
omit [DecidableEq E] in
lemma pick_part (part : E→Fin a) (o : Fin a→E) (ho : ∀ j,part (o j)=j) (xs : List E) (j : Fin a) :
    part (pick part o xs j)=j := by
  unfold pick
  cases he : xs.filter (fun e=>part e=j) with
  | nil=>exact ho j
  | cons e es=>
    have hm : e∈xs.filter (fun e=>part e=j) := by rw [he]; exact List.mem_cons_self
    exact of_decide_eq_true (List.mem_filter.mp hm).2
lemma pick_covers (part : E→Fin a) (o : Fin a→E) (xs : List E)
    (hX : ∀ j,(xs.toFinset.filter (fun e=>part e=j)).card≤1) (e : E) (he : e∈xs) :
    pick part o xs (part e)=e := by
  unfold pick
  have hm : e∈xs.filter (fun x=>part x=part e) := List.mem_filter.mpr ⟨he,by simp only [decide_true]⟩
  cases hx : xs.filter (fun x=>part x=part e) with
  | nil=>rw [hx] at hm; exact False.elim (List.not_mem_nil hm)
  | cons f fs=>
    have hf : f∈xs.filter (fun x=>part x=part e) := by rw [hx]; exact List.mem_cons_self
    have hf' := List.mem_filter.mp hf
    change f=e
    exact (Finset.card_le_one.mp (hX (part e))) f
      (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hf'.1,of_decide_eq_true hf'.2⟩) e
      (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr he,rfl⟩)
def filled (part : E→Fin a) (o : Fin a→E) (loc : E→V) (xs : List E) : Finset V :=
  Finset.univ.image (loc ∘ pick part o xs)
omit [DecidableEq E] in
lemma filled_subset (F : Finset V) (part : E→Fin a) (o : Fin a→E) (loc : E→V)
    (hloc : ∀ e,loc e∈F) (xs : List E) : filled part o loc xs⊆F := by
  intro x hx
  obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hx
  exact hloc _
omit [DecidableEq E] in
lemma filled_card (part : E→Fin a) (o : Fin a→E) (loc : E→V) (xs : List E) :
    (filled part o loc xs).card≤a := (Finset.card_image_le).trans (by simp)
lemma filled_covers (part : E→Fin a) (o : Fin a→E) (loc : E→V) (xs : List E)
    (hX : ∀ j,(xs.toFinset.filter (fun e=>part e=j)).card≤1) : ∀ e∈xs.toFinset,loc e∈filled part o loc xs := by
  intro e he
  exact Finset.mem_image.mpr ⟨part e,Finset.mem_univ _,by
    simp only [Function.comp_apply,pick_covers part o xs hX e (List.mem_toFinset.mp he)]⟩
omit [DecidableEq E] in
lemma filled_ball [PseudoMetricSpace V] (part : E→Fin a) (o : Fin a→E) (ho : ∀ j,part (o j)=j)
    (loc : E→V) (w : Fin a→V) (radius : Fin a→ℝ)
    (hball : ∀ e,dist (w (part e)) (loc e)≤radius (part e)) (xs : List E) :
    ∀ i,∃ x∈filled part o loc xs,dist (w i) x≤radius i := by
  intro i
  refine ⟨loc (pick part o xs i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,?_⟩
  simpa only [pick_part part o ho xs] using hball (pick part o xs i)
end MetricKMedianRecovery.Completion.Canonical
namespace MetricKMedianRecovery.Completion.Canonical
variable {V : Type*} [LinearOrder V]
def pad (F U : Finset V) (n : ℕ) : Finset V := U∪bottomSet (F\U) (n-U.card)
lemma subset_pad (F U : Finset V) (n : ℕ) : U⊆pad F U n := Finset.subset_union_left
lemma pad_subset (F U : Finset V) (n : ℕ) (hUF : U⊆F) : pad F U n⊆F :=
  Finset.union_subset hUF ((bottomSet_subset _ _).trans Finset.sdiff_subset)
lemma pad_card (F U : Finset V) (n : ℕ) (hUF : U⊆F) (hUn : U.card≤n) (hnF : n≤F.card) :
    (pad F U n).card=n := by
  have hd : Disjoint U (bottomSet (F\U) (n-U.card)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    exact (Finset.mem_sdiff.mp (bottomSet_subset _ _ hb)).2 hx
  rw [pad,Finset.card_union_of_disjoint hd,bottomSet_card,Finset.card_sdiff_of_subset hUF,
    min_eq_left (Nat.sub_le_sub_right hnF _)]
  omega
lemma pad_nonempty (F U : Finset V) (n : ℕ) (hUF : U⊆F) (hUn : U.card≤n) (hnF : n≤F.card) (hn : 0<n) :
    (pad F U n).Nonempty := Finset.card_pos.mp (by rw [pad_card F U n hUF hUn hnF]; exact hn)
end MetricKMedianRecovery.Completion.Canonical

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionPad
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
def pack (F U : Finset ℕ) (n : ℕ) : List Bool :=
  encode [BinaryNatSet.encode F,BinaryNatSet.encode U,n.bits]
noncomputable def need (x : List Bool) : List Bool := (value (field 2 x)-value (lengthBits (field 1 x))).bits
noncomputable def need_computes : PolyComputes need := NatOps.sub (field_computes 2) ((field_computes 1).comp lengthBits_computes)
noncomputable def remaining (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (field 0 x,field 1 x))
noncomputable def remaining_computes : PolyComputes remaining := ((field_computes 0).pair (field_computes 1)).comp BinaryNatSet.diff_computes
noncomputable def run (x : List Bool) : List Bool := BinaryNatSet.union (pairBits (field 1 x,Take.run (pairBits (need x,remaining x))))
attribute [local irreducible] need remaining BinaryNatSet.union Take.run
noncomputable def run_computes : PolyComputes run :=
  ((field_computes 1).pair ((need_computes.pair remaining_computes).comp Take.run_computes)).comp BinaryNatSet.union_computes
lemma need_pack (F U : Finset ℕ) (n : ℕ) : need (pack F U n)=(n-U.card).bits := by
  simp only [need,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    lengthBits_encode,value_bits,List.length_map,Finset.length_sort]
lemma remaining_pack (F U : Finset ℕ) (n : ℕ) : remaining (pack F U n)=BinaryNatSet.encode (F\U) := by
  simp only [remaining,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryNatSet.diff_encode]
lemma run_pack (F U : Finset ℕ) (n : ℕ) : run (pack F U n)=BinaryNatSet.encode (Completion.Canonical.pad F U n) := by
  rw [run,need_pack,remaining_pack]
  have hf : field 1 (pack F U n)=BinaryNatSet.encode U := by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hf,Take.run_encode,←List.map_take,BinaryNatSet.union_pack,Finset.sort_toFinset]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryCompletionPad

end OAI

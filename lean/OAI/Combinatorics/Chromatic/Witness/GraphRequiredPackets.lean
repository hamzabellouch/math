import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.Admissible
import OAI.Combinatorics.Chromatic.Histories.SortedFiberPerm

namespace OAI

section
namespace ElementaryPositivity.NaturalUnitIntervalGraph
open Packets
open scoped BigOperators
open Classical
noncomputable section
variable {n:ℕ} (G:NaturalUnitIntervalGraph n)

def nonedgeLT (a b:Fin n):Prop:=a<b ∧ ¬G.Edge a b
lemma nonedgeLT_trans : ∀ ⦃first middle last : Fin n⦄,
    G.nonedgeLT first middle → G.nonedgeLT middle last → G.nonedgeLT first last := by
  intro a b c hab hbc
  refine ⟨hab.1.trans hbc.1,?_⟩
  intro hac
  rcases hac with hac|hca
  · exact hab.2 (Or.inl ⟨hab.1,hbc.1.le.trans hac.2⟩)
  · exact (not_lt_of_ge (hab.1.trans hbc.1).le) hca.1

def wordMask (w:Equiv.Perm (Fin n)):=ascentMask G.nonedgeLT w
lemma wordMask_empty (w:Equiv.Perm (Fin n)) : G.wordMask w=∅ ↔ G.Admissible w := by
  constructor
  · intro he i j hij hlt
    by_contra hn
    let t:Fin (n-1):=⟨i.val,by omega⟩
    have hi:left t=i:=Fin.ext rfl
    have hj:right t=j:=Fin.ext hij
    have ht:t∈G.wordMask w:=(mem_ascentMask _ _ _).mpr (by change _ < _ ∧ ¬_; simpa only [hi,hj] using And.intro hlt hn)
    rw [he] at ht
    exact Finset.notMem_empty t ht
  · intro hw
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact ((mem_ascentMask _ _ _).mp ht).2
      (hw (left t) (right t) rfl ((mem_ascentMask _ _ _).mp ht).1)

lemma required_sorted (J:Finset (Fin (n-1))) (w:Equiv.Perm (Fin n))
    (hw:J⊆G.wordMask w):Sorted (index J) w:=by
  intro i j he hij
  exact (inside_of_required G.nonedgeLT G.nonedgeLT_trans J w hw i j hij he).1
lemma required_proper (J:Finset (Fin (n-1))) (w:Equiv.Perm (Fin n))
    (hw:J⊆G.wordMask w):G.Proper (fun a=>index J (w.symm a)):=by
  intro a b hab he
  rcases lt_trichotomy (w.symm a) (w.symm b) with h|h|h
  · have H:=inside_of_required G.nonedgeLT G.nonedgeLT_trans J w hw _ _ h he
    exact H.2 (by simpa only [w.apply_symm_apply] using hab)
  · have hh:a=b:=w.symm.injective h
    subst b
    exact G.edge_irrefl a hab
  · have H:=inside_of_required G.nonedgeLT G.nonedgeLT_trans J w hw _ _ h he.symm
    exact H.2 (by simpa only [w.apply_symm_apply] using (G.edge_comm a b).mp hab)

lemma required_of_sorted (J:Finset (Fin (n-1))) (κ:Fin n → Fin (n+1))
    (hκ:G.Proper κ) (w:Equiv.Perm (Fin n)) (hw:∀i,κ (w i)=index J i)
    (hs:Sorted (index J) w) : J⊆G.wordMask w := by
  intro t ht
  apply (mem_ascentMask _ _ _).mpr
  have he:index J (left t)=index J (right t):=(index_left_right J t).mpr ht
  refine ⟨hs _ _ he (by change t.val<t.val+1; omega),?_⟩
  intro hedge
  exact hκ _ _ hedge (by rw [hw,hw,he])

abbrev RequiredWord (J:Finset (Fin (n-1))):= {w:Equiv.Perm (Fin n) // J⊆G.wordMask w}
abbrev PacketColor (J:Finset (Fin (n-1))):=
  {κ:Fin n → Fin (n+1) // G.Proper κ ∧ ∀c,card κ c=card (index J) c}

def requiredColorEquiv (J:Finset (Fin (n-1))) : G.RequiredWord J ≃ G.PacketColor J where
  toFun w:=⟨fun a=>index J (w.val.symm a),G.required_proper J w.val w.property,
    fun c=>(card_of_perm (index J) (fun a=>index J (w.val.symm a)) w.val (by intro i; simp) c).symm⟩
  invFun κ:=⟨sortedPerm (index J) κ.val (fun c=>(κ.property.2 c).symm),
    G.required_of_sorted J κ.val κ.property.1 _ (sortedPerm_map _ _ _) (sortedPerm_sorted _ _ _)⟩
  left_inv w:=by
    apply Subtype.ext
    change sortedPerm (index J) (fun a=>index J (w.val.symm a)) _=w.val
    apply sorted_unique (index J) (fun a=>index J (w.val.symm a))
    · exact sortedPerm_map (index J) (fun a=>index J (w.val.symm a)) _
    · intro i; simp
    · exact sortedPerm_sorted (index J) (fun a=>index J (w.val.symm a)) _
    · exact G.required_sorted _ _ w.property
  right_inv κ:=by
    apply Subtype.ext
    funext a
    have H:=sortedPerm_map (index J) κ.val (fun c=>(κ.property.2 c).symm)
      ((sortedPerm (index J) κ.val (fun c=>(κ.property.2 c).symm)).symm a)
    simpa only [Equiv.apply_symm_apply] using H.symm

lemma packet_energy (J:Finset (Fin (n-1))) (κ:Fin n → Fin (n+1))
    (hκ:G.Proper κ) (w:Equiv.Perm (Fin n)) (hw:∀i,κ (w i)=index J i) :
    G.coloringInversions κ=G.graphInversions w := by
  rw [G.graphInversions_eq_card_invertedEdges,coloringInversions,invertedEdges]
  congr 1
  apply Finset.filter_congr
  intro ab hab
  have hedge:G.Edge ab.1 ab.2:=(Finset.mem_filter.mp hab).2.2
  have hne:κ ab.1≠κ ab.2:=hκ _ _ hedge
  have hcolor:∀a,κ a=index J (w.symm a):=fun a=>by simpa using hw (w.symm a)
  rw [hcolor ab.1,hcolor ab.2] at hne ⊢
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (index_mono J (le_of_not_gt hn))) h
  · intro h
    exact lt_of_le_of_ne (index_mono J h.le) hne.symm

lemma requiredColorEquiv_energy (J:Finset (Fin (n-1))) (w:G.RequiredWord J) :
    G.coloringInversions (G.requiredColorEquiv J w).val=G.graphInversions w.val:=by
  apply G.packet_energy J _ (G.required_proper J w.val w.property) w.val
  intro i
  simp
end
end ElementaryPositivity.NaturalUnitIntervalGraph

end

end OAI

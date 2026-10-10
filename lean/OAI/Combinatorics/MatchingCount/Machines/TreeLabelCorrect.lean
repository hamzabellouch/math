import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.LabelOrder
import OAI.Combinatorics.MatchingCount.Machines.TreeLabelTable

namespace OAI

namespace MatchingFPRAS.UnitRefresh
lemma ofFn_orderedEnum (A : Type) [Fintype A] [LinearOrder A] :
    List.ofFn (orderedEnum A)=(Finset.univ : Finset A).sort (· ≤ ·) := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    simp only [List.getElem_ofFn]
    rfl
end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Finset

abbrev key {n H : ℕ} {B : Fin n→Fin n→ℚ} (l : NumberedHierarchy.Label B H) : LabelKey := (l.1.val,l.2.val.val)
lemma key_injective {n H : ℕ} (B : Fin n→Fin n→ℚ) : Function.Injective (key (B:=B) (H:=H)) := by
  rintro ⟨k,a⟩ ⟨j,b⟩ he
  have he' : k=j := Fin.ext (congrArg Prod.fst he)
  cases he'
  exact congrArg (Sigma.mk k) (Subtype.ext (Fin.ext (congrArg Prod.snd he)))

lemma labels_pairwise (x : HierarchyInput) :
    (labels x).Pairwise (fun a b=>toLex a < toLex b) := by
  apply List.Pairwise.filter
  apply List.pairwise_flatMap.mpr
  constructor
  · intro k _
    apply List.pairwise_map.mpr
    exact (List.pairwise_lt_range (n:=x.1.length)).imp (fun h=>by exact Prod.Lex.right _ h)
  · apply (List.pairwise_lt_range (n:=x.2.length+1)).imp
    intro k j hkj a ha b hb
    obtain ⟨u,_,rfl⟩:=List.mem_map.mp ha
    obtain ⟨v,_,rfl⟩:=List.mem_map.mp hb
    exact Prod.Lex.left _ _ hkj

lemma mem_labels_iff_key {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) (l : LabelKey) :
    l∈labels (matrixRep B,xs) ↔ ∃ a : NumberedHierarchy.Label B xs.length,key a=l := by
  rw [mem_labels,matrixRep_length]
  dsimp only
  constructor
  · rintro ⟨hk,hv,hr⟩
    let k : Fin (xs.length+1):=⟨l.1,by omega⟩
    let v : Fin n:=⟨l.2,hv⟩
    have hr' : NumberedHierarchy.root B ((2:ℚ)^k.val) v=v := by
      apply Fin.ext
      exact (labelRoot_matrixRep B hB xs k v).symm.trans hr
    exact ⟨⟨k,⟨v,hr'⟩⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨Nat.le_of_lt_succ a.1.isLt,a.2.val.isLt,(labelRoot_matrixRep B hB xs a.1 a.2.val).trans (congrArg Fin.val a.2.property)⟩

local instance {n H : ℕ} (B : Fin n→Fin n→ℚ) : LinearOrder (NumberedHierarchy.Label B H) := NumberedHierarchy.labelOrder B H
local instance (priority := 2000) {n H : ℕ} (B : Fin n→Fin n→ℚ) : LE (NumberedHierarchy.Label B H) := (NumberedHierarchy.labelOrder B H).toLE
lemma key_le_iff {n H : ℕ} (B : Fin n→Fin n→ℚ) (a b : NumberedHierarchy.Label B H) :
    toLex (key a) ≤ toLex (key b) ↔ a ≤ b := by
  change _ ↔ toLex (a.1,a.2.val) ≤ toLex (b.1,b.2.val)
  simp only [Prod.Lex.le_iff,key,Fin.lt_def,Fin.le_def]
  exact or_congr Iff.rfl (and_congr Fin.val_inj Iff.rfl)
lemma labels_eq_sorted_keys {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) :
    labels (matrixRep B,xs)=((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key := by
  let R : LabelKey→LabelKey→Prop:=fun a b=>toLex a ≤ toLex b
  have ha : (labels (matrixRep B,xs)).Pairwise R := (labels_pairwise _).imp (fun h=>h.le)
  have hb : (((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key).Pairwise R := by
    apply List.pairwise_map.mpr
    exact (Finset.pairwise_sort _ _).imp (fun h=>(key_le_iff B _ _).mpr h)
  have hn : (labels (matrixRep B,xs)).Nodup :=
    (labels_pairwise _).imp (fun h he=>h.ne (congrArg toLex he))
  have hm : (((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key).Nodup :=
    (Finset.sort_nodup _ _).map (key_injective B)
  have hp : (labels (matrixRep B,xs)).Perm (((univ : Finset (NumberedHierarchy.Label B xs.length)).sort (· ≤ ·)).map key) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hn hm
    ext l
    simp only [List.mem_toFinset,mem_labels_iff_key B hB,List.mem_map,Finset.mem_sort,Finset.mem_univ,true_and]
  exact hp.eq_of_pairwise (fun a b _ _ hab hba=>toLex.injective (le_antisymm hab hba)) ha hb
lemma labels_eq_ofFn {n : ℕ} (B : Fin n→Fin n→ℚ) (hB : ∀ a b,0 ≤ B a b)
    (xs : List Bool) :
    labels (matrixRep B,xs)=List.ofFn (fun i=>key (UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length) i)) := by
  change _=List.ofFn (key ∘ UnitRefresh.orderedEnum (NumberedHierarchy.Label B xs.length))
  rw [←List.map_ofFn,UnitRefresh.ofFn_orderedEnum,labels_eq_sorted_keys B hB]
end MatchingFPRAS.ExecutableHierarchy

end OAI

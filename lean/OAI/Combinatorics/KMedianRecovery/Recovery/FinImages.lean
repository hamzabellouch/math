import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.RationalBottomIndices

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {m n : ℕ}
def table (f : Fin m→Fin n) : List Bool := WordList.encode (List.ofFn (fun i=>(f i).val.bits))
lemma sort_list (xs : List (Fin n)) :
    BinaryNatSet.sort (WordList.encode (xs.map (fun i=>i.val.bits)))=encode xs.toFinset := by
  have hh:=BinaryNatSet.sort_pack (xs.map Fin.val)
  simp only [BinaryNatSet.pack,List.map_map,Function.comp_def] at hh
  rw [hh,encode]
  congr 1
  ext i
  simp only [List.mem_toFinset,List.mem_map,values,Finset.mem_image,List.mem_toFinset]
lemma sort_table (f : Fin m→Fin n) : BinaryNatSet.sort (table f)=encode (Finset.univ.image f) := by
  have hh:=sort_list (List.ofFn f)
  simp only [List.map_ofFn,Function.comp_def] at hh
  rw [table,hh]
  congr 1
  ext i
  simp
noncomputable def image : List Bool→List Bool := BinaryNatSet.sort ∘ BinaryIndexMap.run
noncomputable def image_computes : PolyComputes image := BinaryIndexMap.run_computes.comp BinaryNatSet.sort_computes
lemma image_list (f : Fin m→Fin n) (xs : List (Fin m)) :
    image (pairBits (table f,WordList.encode (xs.map (fun i=>i.val.bits))))=encode (xs.toFinset.image f) := by
  unfold image table
  rw [Function.comp_apply,BinaryIndexMap.run_pack]
  have hh:=sort_list (xs.map f)
  simp only [List.map_map,Function.comp_def] at hh ⊢
  rw [hh]
  congr 1
  ext i
  simp
lemma image_ofFn {l : ℕ} (f : Fin m→Fin n) (g : Fin l→Fin m) :
    image (pairBits (table f,WordList.encode (List.ofFn (fun j=>(g j).val.bits))))=
      encode (Finset.univ.image (f ∘ g)) := by
  have hh:=image_list f (List.ofFn g)
  simp only [List.map_ofFn,Function.comp_def] at hh
  rw [hh]
  congr 1
  ext i
  simp
lemma image_pack (f : Fin m→Fin n) (S : Finset (Fin m)) :
    image (pairBits (table f,encode S))=encode (S.image f) := by
  rw [encode_eq,image_list,Finset.sort_toFinset]
lemma bottom_pack (v : Fin m→ℚ) (k : ℕ) :
    BinaryNatSet.sort (BinaryRationalSort.rawIndices
      (pairBits (k.bits,WordList.encode (List.ofFn (fun i=>BinaryRational.encode (v i))))))=
      encode (BinaryRationalSort.indexSet v k) := by
  rw [BinaryRationalSort.rawIndices_pack,BinaryNatSet.sort_pack,BinaryRationalSort.bottomIndices_finset]
  rfl
lemma encode_lengthBits (S : Finset (Fin n)) : lengthBits (encode S)=S.card.bits := by
  rw [encode_eq,lengthBits_encode,List.length_map,Finset.length_sort]
end MetricKMedianRecovery.BitMachine.BinaryFinSet

namespace MetricKMedianRecovery.BitMachine.BinaryTaggedSets
open WordOperations WordList BinaryArithmetic
variable {n : ℕ}
def left (i : Fin n) : Fin (n+n) := Fin.castLE (Nat.le_add_right n n) i
def right (i : Fin n) : Fin (n+n) := Fin.natAdd n i
lemma left_encode (S : Finset (Fin n)) : BinaryFinSet.encode (S.image left)=BinaryFinSet.encode S := by
  simp only [BinaryFinSet.encode,BinaryFinSet.values,Finset.image_image]
  rfl
noncomputable def plus (x : List Bool) : List Bool := (value (extractPrefix x)+value (discardPrefix x)).bits
noncomputable def plus_computes : PolyComputes plus := NatOps.add extractPrefix_computes discardPrefix_computes
noncomputable def shift : List Bool→List Bool := BinaryNatSet.sort ∘ mapWith plus
noncomputable def shift_computes : PolyComputes shift := (mapWith_computes plus_computes).comp BinaryNatSet.sort_computes
lemma shift_encode (S : Finset (Fin n)) :
    shift (pairBits (n.bits,BinaryFinSet.encode S))=BinaryFinSet.encode (S.image right) := by
  rw [shift,Function.comp_apply,BinaryFinSet.encode_eq,mapWith_encode,List.map_map]
  simp only [Function.comp_def]
  have he : ((S.sort (·≤·)).map (fun i=>plus (pairBits (n.bits,i.val.bits))))=
      ((S.sort (·≤·)).map right).map (fun i=>i.val.bits) := by
    simp only [List.map_map,Function.comp_def,plus,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,right,Fin.val_natAdd]
  rw [he,BinaryFinSet.sort_list]
  congr 1
  ext i
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_image]
noncomputable def minus (x : List Bool) : List Bool := (value (discardPrefix x)-value (extractPrefix x)).bits
noncomputable def minus_computes : PolyComputes minus := NatOps.sub discardPrefix_computes extractPrefix_computes
noncomputable def unshift : List Bool→List Bool := BinaryNatSet.sort ∘ mapWith minus
noncomputable def unshift_computes : PolyComputes unshift := (mapWith_computes minus_computes).comp BinaryNatSet.sort_computes
lemma unshift_encode (S : Finset (Fin n)) :
    unshift (pairBits (n.bits,BinaryFinSet.encode (S.image right)))=BinaryFinSet.encode S := by
  rw [unshift,Function.comp_apply,BinaryFinSet.encode_eq,mapWith_encode,List.map_map]
  simp only [Function.comp_def]
  let xs:=((S.image right).sort (·≤·)).map (fun i=>i.val-n)
  have hh:=BinaryNatSet.sort_pack xs
  simp only [BinaryNatSet.pack,xs,List.map_map,Function.comp_def] at hh
  simp only [minus,extractPrefix_pairBits,discardPrefix_pairBits,value_bits]
  rw [hh,BinaryFinSet.encode]
  congr 1
  ext a
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_image,BinaryFinSet.values]
  constructor
  · rintro ⟨i,⟨j,hj,rfl⟩,rfl⟩
    exact ⟨j,hj,by simp [right]⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨right j,⟨j,hj,rfl⟩,by simp [right]⟩
lemma disjoint (A B : Finset (Fin n)) : Disjoint (A.image left) (B.image right) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hi
  obtain ⟨b,hb,he⟩:=Finset.mem_image.mp hj
  have h:=congrArg Fin.val he
  simp only [left,right,Fin.val_castLE,Fin.val_natAdd] at h
  omega
end MetricKMedianRecovery.BitMachine.BinaryTaggedSets

end OAI

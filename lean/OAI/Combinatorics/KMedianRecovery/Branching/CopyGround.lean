import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FinImages
import OAI.Combinatorics.KMedianRecovery.Recovery.PartitionPullback

namespace OAI

namespace MetricKMedianRecovery.Completion.CopyGround
variable {n a : ℕ}
def part : Fin (a*n)→Fin a := Fin.divNat
noncomputable def location (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (e : Fin (a*n)) : Fin n :=
  if e.modNat ∈ H e.divNat then e.modNat else (H e.divNat).min' (hH e.divNat)
lemma location_mem (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (e : Fin (a*n)) :
    location H hH e ∈ H (part e) := by
  unfold location part
  split_ifs with h
  · exact h
  · exact Finset.min'_mem _ _
def embed (H : Fin a→Finset (Fin n)) (e : (i : Fin a)×(H i)) : Fin (a*n) := finProdFinEquiv (e.1,e.2.val)
lemma part_embed (H : Fin a→Finset (Fin n)) (e : (i : Fin a)×(H i)) : part (embed H e)=e.1 := by
  exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (e.1,e.2.val))
lemma mod_embed (H : Fin a→Finset (Fin n)) (e : (i : Fin a)×(H i)) : (embed H e).modNat=e.2.val := by
  exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (e.1,e.2.val))
lemma location_embed (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (e : (i : Fin a)×(H i)) :
    location H hH (embed H e)=e.2.val := by
  simp only [location,mod_embed,show (embed H e).divNat=e.1 from part_embed H e,ite_eq_left e.2.property]
noncomputable def origin (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (i : Fin a) : Fin (a*n) :=
  embed H ⟨i,⟨(H i).min' (hH i),Finset.min'_mem _ _⟩⟩
lemma part_origin (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (i : Fin a) : part (origin H hH i)=i :=
  part_embed H _
lemma part_surjective (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) : Function.Surjective (part (n:=n) (a:=a)) :=
  fun i=>⟨origin H hH i,part_origin H hH i⟩
lemma lift_feasible (H : Fin a→Finset (Fin n)) (X : Finset ((i : Fin a)×(H i)))
    (hX : Categorical.PartitionFeasible Sigma.fst X) : Categorical.PartitionFeasible part (X.image (embed H)) :=
  partition_image Sigma.fst part (embed H) (part_embed H) X hX
end MetricKMedianRecovery.Completion.CopyGround
namespace MetricKMedianRecovery.Completion
variable {E B P R : Type*} [DecidableEq E] [DecidableEq B] [Fintype P] [Fintype R]
omit [DecidableEq E] in
lemma surrogate_image (K : ℝ) (q : ℕ) (base : P→ℝ) (distance : P→B→ℝ)
    (weight redBase : R→ℝ) (redDistance : R→B→ℝ) (f : E→B) (X : Finset E) :
    surrogate K q base distance weight redBase redDistance (X.image f)=
      surrogate K q base (fun p=>distance p ∘ f) weight redBase (fun r=>redDistance r ∘ f) X := by
  simp only [surrogate,capped_image]
end MetricKMedianRecovery.Completion

namespace MetricKMedianRecovery.BitMachine.BinaryCopyTables
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes field_encode)
variable {n a : ℕ}
def pack (H : Fin a→Finset (Fin n)) : List Bool :=
  encode [List.replicate n true,encode (List.ofFn (fun i=>BinaryFinSet.encode (H i)))]
noncomputable def ball (x : List Bool) : List Bool := Lookup.run
  (pairBits (discardPrefix x,field 1 (extractPrefix x)))
noncomputable def ball_computes : PolyComputes ball :=
  (discardPrefix_computes.pair (extractPrefix_computes.comp (field_computes 1))).comp Lookup.run_computes
noncomputable def entry (x : List Bool) : List Bool :=
  if BinaryNatSet.contains (pairBits (discardPrefix x,extractPrefix x)) then discardPrefix x
  else head (extractPrefix x)
noncomputable def entry_computes : PolyComputes entry :=
  (((discardPrefix_computes.pair extractPrefix_computes).comp BinaryNatSet.contains_computes).cond
    discardPrefix_computes (extractPrefix_computes.comp WordList.head_computes))
noncomputable def columns (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (field 0 (extractPrefix x))
noncomputable def columns_computes : PolyComputes columns :=
  ((extractPrefix_computes.comp (field_computes 0)).comp BinaryEllipsoidInitial.indices_computes)
noncomputable def row (x : List Bool) : List Bool := mapWith entry (pairBits (ball x,columns x))
attribute [local irreducible] mapWith flatMapWith
noncomputable def row_computes : PolyComputes row := by
  unfold row
  exact (ball_computes.pair columns_computes).comp (mapWith_computes entry_computes)
noncomputable def indices (x : List Bool) : List Bool := BinaryEllipsoidInitial.indices (Count.run (field 1 x))
noncomputable def indices_computes : PolyComputes indices := ((field_computes 1).comp Count.run_computes).comp BinaryEllipsoidInitial.indices_computes
noncomputable def locations (x : List Bool) : List Bool := flatMapWith row (pairBits (x,indices x))
noncomputable def locations_computes : PolyComputes locations := by
  unfold locations
  exact (id_computes.pair indices_computes).comp (flatMapWith_computes row_computes)
noncomputable def partRow (x : List Bool) : List Bool := mapWith extractPrefix (pairBits (discardPrefix x,columns x))
noncomputable def partRow_computes : PolyComputes partRow := by
  unfold partRow
  exact (discardPrefix_computes.pair columns_computes).comp (mapWith_computes extractPrefix_computes)
noncomputable def parts (x : List Bool) : List Bool := flatMapWith partRow (pairBits (x,indices x))
noncomputable def parts_computes : PolyComputes parts := by
  unfold parts
  exact (id_computes.pair indices_computes).comp (flatMapWith_computes partRow_computes)
noncomputable def origin (x : List Bool) : List Bool :=
  (((field 0 (extractPrefix x)).length)*value (discardPrefix x)+value (head (ball x))).bits
noncomputable def origin_computes : PolyComputes origin := by
  unfold origin
  simpa only [Function.comp_def,UnaryResources.lengthBits_eq,value_bits] using NatOps.add
    (NatOps.mul (((extractPrefix_computes.comp (field_computes 0)).comp UnaryResources.lengthBits_computes)) discardPrefix_computes)
    (ball_computes.comp WordList.head_computes)

noncomputable def origins (x : List Bool) : List Bool := mapWith origin (pairBits (x,indices x))
noncomputable def origins_computes : PolyComputes origins := by
  unfold origins
  exact (id_computes.pair indices_computes).comp (mapWith_computes origin_computes)
lemma head_set (H : Finset (Fin n)) (hH : H.Nonempty) : head (BinaryFinSet.encode H)=(H.min' hH).val.bits := by
  rw [BinaryFinSet.encode_eq]
  have hn : H.sort (·≤·)≠[] := by
    intro he
    have hh:=Finset.length_sort (s:=H) (·≤·)
    rw [he] at hh
    exact hH.card_pos.ne' hh.symm
  obtain ⟨h,t,he⟩:=List.exists_cons_of_ne_nil hn
  rw [he,List.map_cons,encode,head_cons]
  have hm : h=H.min' hH := by
    have hh:=@Finset.sorted_zero_eq_min' (Fin n) _ H (by rw [Finset.length_sort];exact hH.card_pos)
    simpa only [he,List.getElem_cons_zero] using hh
  rw [hm]
lemma contains_set (H : Finset (Fin n)) (j : Fin n) :
    BinaryNatSet.contains (pairBits (j.val.bits,BinaryFinSet.encode H))=decide (j∈H) := by
  rw [BinaryFinSet.encode_eq]
  have hh:=BinaryNatSet.contains_pack j.val ((H.sort (·≤·)).map Fin.val)
  simp only [BinaryNatSet.pack,List.map_map,Function.comp_def] at hh
  rw [hh]
  congr 1
  simp only [List.mem_map,Finset.mem_sort,Fin.val_inj,exists_eq_right]
lemma ball_pack (H : Fin a→Finset (Fin n)) (i : Fin a) : ball (pairBits (pack H,i.val.bits))=BinaryFinSet.encode (H i) := by
  simp only [ball,extractPrefix_pairBits,discardPrefix_pairBits,pack,field_encode,
    List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,lookup_ofFn]
lemma columns_pack (H : Fin a→Finset (Fin n)) (w : List Bool) :
    columns (pairBits (pack H,w))=encode (List.ofFn (fun j : Fin n=>j.val.bits)) := by
  simp only [columns,extractPrefix_pairBits,pack,field_encode,List.getElem?_cons_zero,Option.getD_some,BinaryEllipsoidInitial.indices_replicate]
lemma indices_pack (H : Fin a→Finset (Fin n)) : indices (pack H)=encode (List.ofFn (fun i : Fin a=>i.val.bits)) := by
  simp only [indices,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,Count.run_encode,List.length_ofFn,
    BinaryEllipsoidInitial.indices_replicate]
lemma entry_pack (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (i : Fin a) (j : Fin n) :
    entry (pairBits (BinaryFinSet.encode (H i),j.val.bits))=
      (Completion.CopyGround.location H hH (finProdFinEquiv (i,j))).val.bits := by
  simp only [entry,extractPrefix_pairBits,discardPrefix_pairBits,contains_set,decide_eq_true_eq,head_set _ (hH i)]
  have hd : (finProdFinEquiv (i,j)).divNat=i := congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i,j))
  have hm : (finProdFinEquiv (i,j)).modNat=j := congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (i,j))
  simp only [Completion.CopyGround.location,hd,hm]
  split_ifs <;> rfl
lemma row_pack (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) (i : Fin a) :
    row (pairBits (pack H,i.val.bits))=encode (List.ofFn (fun j : Fin n=>(Completion.CopyGround.location H hH (finProdFinEquiv (i,j))).val.bits)) := by
  rw [row,ball_pack,columns_pack,mapWith_ofFn]
  simp only [entry_pack H hH]
lemma encoded_ofFn_flatten {c : ℕ} (f : Fin c→List (List Bool)) :
    (List.ofFn (fun i=>encode (f i))).flatten=encode (List.ofFn f).flatten := by
  have hh:=Flatten.encode_flatMap (List.ofFn (fun i : Fin c=>i)) f
  simpa only [List.flatMap,List.map_ofFn,Function.comp_def] using hh.symm
lemma equiv_mk (i : Fin a) (j : Fin n) :
    finProdFinEquiv (i,j)=⟨i.val*n+j.val,by nlinarith [i.isLt,j.isLt]⟩ := by
  apply Fin.ext
  simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
lemma locations_pack (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) :
    locations (pack H)=BinaryFinSet.table (Completion.CopyGround.location H hH) := by
  simp only [locations,indices_pack,flatMapWith,Function.comp_apply,mapWith_ofFn]
  simp only [row_pack H hH,Flatten.run_encode]
  rw [encoded_ofFn_flatten]
  rw [BinaryFinSet.table,List.ofFn_mul]
  simp only [equiv_mk]
lemma parts_pack (H : Fin a→Finset (Fin n)) : parts (pack H)=BinaryFinSet.table (Completion.CopyGround.part (n:=n) (a:=a)) := by
  simp only [parts,indices_pack,flatMapWith,Function.comp_apply,mapWith_ofFn]
  simp only [partRow,columns_pack,discardPrefix_pairBits,mapWith_ofFn,extractPrefix_pairBits,Flatten.run_encode]
  rw [encoded_ofFn_flatten]
  rw [BinaryFinSet.table,List.ofFn_mul]
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have he:=congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (i,j))
  rw [equiv_mk] at he
  exact congrArg (fun k : Fin a=>k.val.bits) he.symm
lemma origins_pack (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) :
    origins (pack H)=BinaryFinSet.table (Completion.CopyGround.origin H hH) := by
  rw [origins,indices_pack,mapWith_ofFn]
  simp only [origin,ball_pack,head_set _ (hH _),value_bits]
  simp only [extractPrefix_pairBits,discardPrefix_pairBits,value_bits,pack,field_encode,List.getElem?_cons_zero,Option.getD_some,List.length_replicate]
  simp only [BinaryFinSet.table,Completion.CopyGround.origin,Completion.CopyGround.embed,finProdFinEquiv,Nat.add_comm]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryCopyTables

end OAI

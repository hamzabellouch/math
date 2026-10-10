import OAI.Combinatorics.VariableWL.Procedure

namespace OAI

namespace VariableWL.NumericRefinement

structure Data where
  leftOrder : ℕ
  rightOrder : ℕ
  dimension : ℕ
  leftMatrix : Word
  rightMatrix : Word

def Data.leftCount (D : Data) := D.leftOrder^D.dimension
def Data.rightCount (D : Data) := D.rightOrder^D.dimension
def Data.count (D : Data) := D.leftCount+D.rightCount

def Data.isLeft (D : Data) (a : ℕ) : Bool := decide (a<D.leftCount)
def Data.order (D : Data) (a : ℕ) := if D.isLeft a then D.leftOrder else D.rightOrder
def Data.offset (D : Data) (a : ℕ) := if D.isLeft a then 0 else D.leftCount
def Data.coordinate (D : Data) (a i : ℕ) := TupleAddress.digit (D.order a) (a-D.offset a) i

def Data.replacement (D : Data) (a z i : ℕ) :=
  D.offset a+TupleAddress.replace (D.order a) (a-D.offset a) i z

def Data.edge (D : Data) (a i j : ℕ) : Bool :=
  (if D.isLeft a then D.leftMatrix else D.rightMatrix).getD
    (D.coordinate a i*D.order a+D.coordinate a j) false

def Data.initial (D : Data) (a b : ℕ) : Bool :=
  (List.range D.dimension).all fun i => (List.range D.dimension).all fun j =>
    decide ((D.coordinate a i=D.coordinate a j) ↔ (D.coordinate b i=D.coordinate b j)) &&
      decide (D.edge a i j=D.edge b i j)

def Data.get (D : Data) (R : Word) (a b : ℕ) : Bool := R.getD (a*D.count+b) false

def Data.profile (D : Data) (R : Word) (x y : ℕ × ℕ) : Bool :=
  (List.range D.dimension).all fun i => D.get R (D.replacement x.1 x.2 i) (D.replacement y.1 y.2 i)

def Data.neighbors (D : Data) (a : ℕ) : List (ℕ × ℕ) := (List.range (D.order a)).map (a,·)

def Data.update (D : Data) (R : Word) (a b : ℕ) : Bool :=
  D.get R a b && RefinementTable.sameCounts (D.profile R) (D.neighbors a) (D.neighbors b)

def Data.pack (D : Data) (f : ℕ → ℕ → Bool) : Word :=
  (List.range (D.count*D.count)).map fun p => f (p/D.count) (p%D.count)

def Data.array (D : Data) : ℕ → Word
  | 0 => D.pack D.initial
  | s+1 => D.pack (D.update (D.array s))

def Data.histogram (D : Data) (R : Word) : Bool :=
  RefinementTable.sameCounts (D.get R) (List.range D.leftCount)
    ((List.range D.rightCount).map (D.leftCount+·))

def Data.accepts (D : Data) : Bool := D.histogram (D.array (D.count^2))

 theorem all_range (n : ℕ) (p : ℕ → Bool) :
    (List.range n).all p=true ↔ ∀i:Fin n,p i=true := by
  simp only [List.all_eq_true,List.mem_range]
  exact ⟨fun h i=>h i i.isLt,fun h i hi=>h ⟨i,hi⟩⟩

 theorem ofFn_nat {α : Type} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i:Fin n=>f i)=(List.range n).map f := by
  rw [List.ofFn_eq_map,←List.map_coe_finRange_eq_range,List.map_map]
  rfl

 theorem sameCounts_map {α β : Type} (f : α → β) (eq : β → β → Bool) (xs ys : List α) :
    RefinementTable.sameCounts eq (xs.map f) (ys.map f)=
      RefinementTable.sameCounts (fun a b=>eq (f a) (f b)) xs ys := by
  simp only [RefinementTable.sameCounts,←List.map_append,List.all_map,Function.comp_def,List.filter_map,List.length_map]

open RefinementTable
attribute [local instance] Classical.propDecidable
variable (G H : Graph) (k : ℕ)

noncomputable def data : Data := ⟨G.order,H.order,k,Encoding.matrix G,Encoding.matrix H⟩

def address (x : Entry G H k) := (RefinementArray.numbering G H k x).val

 theorem address_inl (v : Tuple G k) : address G H k (.inl v)=TupleAddress.encode v := rfl
 theorem address_inr (v : Tuple H k) : address G H k (.inr v)=G.order^k+TupleAddress.encode v := rfl

 theorem left_inl (v : Tuple G k) : (data G H k).isLeft (address G H k (.inl v))=true := by
  change decide (TupleAddress.encode v<G.order^k)=true
  exact decide_eq_true (TupleAddress.encode_lt v)

 theorem left_inr (v : Tuple H k) : (data G H k).isLeft (address G H k (.inr v))=false := by
  change decide (G.order^k+TupleAddress.encode v<G.order^k)=false
  exact decide_eq_false (by omega)

 theorem order_inl (v : Tuple G k) : (data G H k).order (address G H k (.inl v))=G.order := by
  rw [Data.order,left_inl]
  rfl
 theorem order_inr (v : Tuple H k) : (data G H k).order (address G H k (.inr v))=H.order := by
  rw [Data.order,left_inr]
  rfl

 theorem coordinate_inl (v : Tuple G k) (i : Fin k) :
    (data G H k).coordinate (address G H k (.inl v)) i.val=(v i).val := by
  rw [Data.coordinate,order_inl,Data.offset,left_inl]
  simp only [ite_true,Nat.sub_zero,address_inl]
  exact TupleAddress.digit_encode v i

 theorem coordinate_inr (v : Tuple H k) (i : Fin k) :
    (data G H k).coordinate (address G H k (.inr v)) i.val=(v i).val := by
  rw [Data.coordinate,order_inr,Data.offset,left_inr]
  simp only [Bool.false_eq_true,ite_false,data,Data.leftCount,address_inr,Nat.add_sub_cancel_left]
  exact TupleAddress.digit_encode v i

 theorem replacement_inl (v : Tuple G k) (z : Fin G.order) (i : Fin k) :
    (data G H k).replacement (address G H k (.inl v)) z.val i.val=
      address G H k (.inl (Function.update v i z)) := by
  rw [Data.replacement,order_inl,Data.offset,left_inl]
  simp only [ite_true,Nat.sub_zero,Nat.zero_add,address_inl]
  exact (TupleAddress.encode_update v i z).symm

 theorem replacement_inr (v : Tuple H k) (z : Fin H.order) (i : Fin k) :
    (data G H k).replacement (address G H k (.inr v)) z.val i.val=
      address G H k (.inr (Function.update v i z)) := by
  rw [Data.replacement,order_inr,Data.offset,left_inr]
  simp only [Bool.false_eq_true,ite_false,data,Data.leftCount,address_inr,Nat.add_sub_cancel_left]
  rw [TupleAddress.encode_update]

 theorem edge_inl (v : Tuple G k) (i j : Fin k) :
    (data G H k).edge (address G H k (.inl v)) i.val j.val=decide (G.graph.Adj (v i) (v j)) := by
  classical
  rw [Data.edge,left_inl,coordinate_inl,coordinate_inl,order_inl]
  change (Encoding.matrix G).getD ((v i).val*G.order+(v j).val) false=_
  exact Encoding.entry_matrix G (v i) (v j)

 theorem edge_inr (v : Tuple H k) (i j : Fin k) :
    (data G H k).edge (address G H k (.inr v)) i.val j.val=decide (H.graph.Adj (v i) (v j)) := by
  classical
  rw [Data.edge,left_inr,coordinate_inr,coordinate_inr,order_inr]
  change (Encoding.matrix H).getD ((v i).val*H.order+(v j).val) false=_
  exact Encoding.entry_matrix H (v i) (v j)

 theorem get_address (R : Word) (x y : Entry G H k) :
    (data G H k).get R (address G H k x) (address G H k y)=RefinementArray.lookup G H k R x y := rfl

end VariableWL.NumericRefinement

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

 def aux (k : ℕ) : Fin (k+1+1) := ⟨k+1,by omega⟩

 theorem front_ne_aux (i : Fin (k+1)) : front k 1 i≠aux k := by
  intro h
  have hv := congrArg Fin.val h
  change i.val=k+1 at hv
  omega

 theorem aux_ne_front (i : Fin (k+1)) : aux k≠front k 1 i := Ne.symm (front_ne_aux i)

 @[simp] theorem extend_aux (s : Stores k) : extend 1 s (aux k)=[] := extend_back _ _ _ (by rfl)

 theorem clear_aux (s : Stores k) : Function.update (extend 1 s) (aux k) []=extend 1 s := by
  rw [←extend_aux s,Function.update_eq_self]

 theorem pushHead (a o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o ((s a).head?.getD false::s o)) (fun _=>1) := by
  have h := action (fun h : Heads k=>one o (.push ((h a).getD false)))
  simpa only [execute_one,Action.apply,heads] using h

 theorem lookup (a ix o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o [(s a).getD (s ix).length false])
      (fun s=>12*(s a).length+11*(s ix).length+3*(s o).length+12) := by
  let a' := front k 1 a
  let i' := front k 1 ix
  let o' := front k 1 o
  let q := aux k
  have hf := seq (copy a' q) (seq (countedPop i' q)
    (seq (clear o') (seq (pushHead q o') (clear q))))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',i',o',q]
    simp only [Function.update_self,Function.update_of_ne (front_ne_aux ix),
      Function.update_of_ne (aux_ne_front o),Function.update_idem,extend_front',List.head?_drop]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
    rfl
  · intro s
    dsimp only [Function.comp_def,a',i',o',q]
    simp only [Function.update_self,Function.update_of_ne (front_ne_aux ix),
      Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),
      extend_front',extend_aux,List.length_nil,List.length_drop]
    omega

end VariableWL.Computation.Stack.Procedure

namespace VariableWL.Computation.Stack.Procedure
open Code
variable {k : ℕ}

 theorem iterate_lengthAdd (a o : Fin (k+1)) (h : a≠o) (n : ℕ) (s : Stores k) :
    ((fun t : Stores k=>Function.update t o (List.replicate (t a).length true++t o))^[n]) s=
      Function.update s o (List.replicate (n*(s a).length) true++s o) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,Function.update_of_ne h,Function.update_self,
      Function.update_idem,←List.append_assoc,←List.replicate_add]
    congr 3
    ring

 theorem multiplyAdd (a b o : Fin (k+1)) (hao : a≠o) :
    Realizes (fun s : Stores k=>Function.update s o
      (List.replicate ((s b).length*(s a).length) true++s o))
      (fun s=>(6*(s a).length+11)*(s b).length+2) := by
  have h := countedLoop_bound b (lengthAdd a o hao) (B := fun s=>6*(s a).length+1)
    (by intro s j _; rw [iterate_lengthAdd a o hao,Function.update_of_ne hao])
  simpa only [iterate_lengthAdd a o hao,Nat.add_assoc] using h

 theorem length (a o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (List.replicate (s a).length true))
      (fun s=>20*((s a).length+(s o).length+1)) := by
  let a' := front k 1 a
  let o' := front k 1 o
  let q := aux k
  have hf := seq (lengthAdd a' q (front_ne_aux a)) (seq (copy q o') (clear q))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),List.length_replicate]
    omega

 theorem add (a b o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (List.replicate ((s a).length+(s b).length) true))
      (fun s=>20*((s a).length+(s b).length+(s o).length+1)) := by
  let a' := front k 1 a
  let b' := front k 1 b
  let o' := front k 1 o
  let q := aux k
  have hf := seq (lengthAdd b' q (front_ne_aux b))
    (seq (lengthAdd a' q (front_ne_aux a)) (seq (copy q o') (clear q)))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux a),Function.update_idem,←List.replicate_add]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux a),Function.update_of_ne (front_ne_aux o),
      Function.update_of_ne (aux_ne_front o),List.length_append,List.length_replicate]
    omega

 theorem subtract (a b o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (List.replicate ((s a).length-(s b).length) true))
      (fun s=>20*((s a).length+(s b).length+(s o).length+1)) := by
  let a' := front k 1 a
  let b' := front k 1 b
  let o' := front k 1 o
  let q := aux k
  have hf := seq (lengthAdd a' q (front_ne_aux a))
    (seq (countedPop b' q) (seq (copy q o') (clear q)))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux b),Function.update_idem,List.drop_replicate]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux b),Function.update_of_ne (front_ne_aux o),
      Function.update_of_ne (aux_ne_front o),List.length_drop,List.length_replicate]
    omega

 theorem multiply (a b o : Fin (k+1)) :
    Realizes (fun s : Stores k=>Function.update s o (List.replicate ((s a).length*(s b).length) true))
      (fun s=>20*((s a).length+1)*((s b).length+1)+3*(s o).length+10) := by
  let a' := front k 1 a
  let b' := front k 1 b
  let o' := front k 1 o
  let q := aux k
  have hf := seq (multiplyAdd a' b' q (front_ne_aux a)) (seq (copy q o') (clear q))
  apply localRegisters 1 hf
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,Nat.mul_comm]
    rw [Function.update_comm (front_ne_aux o),Function.update_idem,clear_aux,extend_update]
  · intro s
    dsimp only [Function.comp_def,a',b',o',q]
    simp only [extend_front',extend_aux,List.append_nil,Function.update_self,
      Function.update_of_ne (front_ne_aux o),Function.update_of_ne (aux_ne_front o),List.length_replicate]
    nlinarith

end VariableWL.Computation.Stack.Procedure

namespace VariableWL.NumericRefinement
open RefinementTable
attribute [local instance] Classical.propDecidable
variable (G H : Graph) (k : ℕ)

abbrev Key := (Tuple G k × Fin G.order) ⊕ (Tuple H k × Fin H.order)

def keyPair : Key G H k → ℕ × ℕ
  | .inl (v,z) => (address G H k (.inl v),z.val)
  | .inr (v,z) => (address G H k (.inr v),z.val)

def keyVector : Key G H k → Vector G H k
  | .inl (v,z) => fun i => .inl (Function.update v i z)
  | .inr (v,z) => fun i => .inr (Function.update v i z)

def keys : Entry G H k → List (Key G H k)
  | .inl v => List.ofFn fun z : Fin G.order => .inl (v,z)
  | .inr v => List.ofFn fun z : Fin H.order => .inr (v,z)

 theorem keys_pair (x : Entry G H k) :
    (keys G H k x).map (keyPair G H k)=(data G H k).neighbors (address G H k x) := by
  cases x with
  | inl v => rw [keys,List.map_ofFn,Data.neighbors,order_inl]; exact ofFn_nat _ _
  | inr v => rw [keys,List.map_ofFn,Data.neighbors,order_inr]; exact ofFn_nat _ _

 theorem keys_vector (x : Entry G H k) :
    (keys G H k x).map (keyVector G H k)=RefinementTable.neighbors G H k x := by
  cases x <;> simp only [keys,List.map_ofFn,RefinementTable.neighbors,Function.comp_def,keyVector]

 theorem replacement_key (a : Key G H k) (i : Fin k) :
    (data G H k).replacement (keyPair G H k a).1 (keyPair G H k a).2 i.val =
      address G H k (keyVector G H k a i) := by
  cases a with
  | inl p => exact replacement_inl G H k p.1 p.2 i
  | inr p => exact replacement_inr G H k p.1 p.2 i

 theorem profile_key (R : Word) (a b : Key G H k) :
    (data G H k).profile R (keyPair G H k a) (keyPair G H k b)=
      vectorEqual G H k (RefinementArray.lookup G H k R) (keyVector G H k a) (keyVector G H k b) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.profile]
  change (List.range k).all _=true ↔ _
  rw [all_range]
  simp only [vectorEqual,List.all_eq_true,List.mem_finRange,forall_const,replacement_key,get_address]

 theorem update_address (R : Word) (a b : Entry G H k) :
    (data G H k).update R (address G H k a) (address G H k b)=
      RefinementTable.update G H k (RefinementArray.lookup G H k R) a b := by
  rw [Data.update,get_address,←keys_pair,←keys_pair,sameCounts_map]
  rw [RefinementTable.update,←keys_vector,←keys_vector,sameCounts_map]
  congr 2
  funext x y
  exact profile_key G H k R x y

 theorem atomic_address (a : Entry G H k) (i j : Fin k) :
    (decide ((data G H k).coordinate (address G H k a) i.val=
      (data G H k).coordinate (address G H k a) j.val),
      (data G H k).edge (address G H k a) i.val j.val)=tagColor G H k 0 a i j := by
  cases a with
  | inl v =>
    rw [coordinate_inl,coordinate_inl,edge_inl]
    change (decide ((v i).val=(v j).val),decide (G.graph.Adj (v i) (v j)))=
      (decide (v i=v j),decide (G.graph.Adj (v i) (v j)))
    simp only [Fin.val_inj]
  | inr v =>
    rw [coordinate_inr,coordinate_inr,edge_inr]
    change (decide ((v i).val=(v j).val),decide (H.graph.Adj (v i) (v j)))=
      (decide (v i=v j),decide (H.graph.Adj (v i) (v j)))
    simp only [Fin.val_inj]

 theorem initial_address (a b : Entry G H k) :
    (data G H k).initial (address G H k a) (address G H k b)=RefinementTable.initial G H k a b := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.initial]
  change (List.range k).all (fun i=>(List.range k).all _)=true ↔ _
  simp only [all_range,Bool.and_eq_true,decide_eq_true_eq,RefinementTable.initial]
  change _ ↔ (fun i j=>tagColor G H k 0 a i j)=(fun i j=>tagColor G H k 0 b i j)
  simp only [funext_iff,←atomic_address,Prod.mk.injEq,decide_eq_decide]

 theorem pack_correct (f : ℕ → ℕ → Bool) (R : Entry G H k → Entry G H k → Bool)
    (h : ∀a b,f (address G H k a) (address G H k b)=R a b) :
    (data G H k).pack f=RefinementArray.pack G H k R := by
  change (List.range (RefinementArray.count G H k*RefinementArray.count G H k)).map _=_
  rw [←ofFn_nat,RefinementArray.pack]
  congr 1
  funext p
  have he := h ((RefinementArray.numbering G H k).symm p.divNat)
    ((RefinementArray.numbering G H k).symm p.modNat)
  unfold address at he
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at he
  exact he

 theorem array_correct (s : ℕ) : (data G H k).array s=RefinementArray.array G H k s := by
  induction s with
  | zero => exact pack_correct G H k _ _ (initial_address G H k)
  | succ s ih =>
    rw [Data.array,RefinementArray.array,ih]
    exact pack_correct G H k _ _ (update_address G H k _)

end VariableWL.NumericRefinement

namespace VariableWL.NumericRefinement
open RefinementTable
attribute [local instance] Classical.propDecidable

 theorem sameCounts_perm {α : Type} (eq : α → α → Bool) {xs ys xs' ys' : List α}
    (hx : xs.Perm xs') (hy : ys.Perm ys') :
    sameCounts eq xs ys=sameCounts eq xs' ys' := by
  unfold sameCounts
  have hf : (fun a=>decide ((xs.filter (eq a)).length=(ys.filter (eq a)).length))=
      (fun a=>decide ((xs'.filter (eq a)).length=(ys'.filter (eq a)).length)) := by
    funext a
    rw [(hx.filter (eq a)).length_eq,(hy.filter (eq a)).length_eq]
  rw [hf]
  exact (hx.append hy).all_eq

 theorem ofFn_perm_univ {α : Type} [Fintype α] {n : ℕ} (e : α ≃ Fin n) :
    (List.ofFn e.symm).Perm (Finset.univ : Finset α).toList := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn_ofInjective e.symm.injective)
    (Finset.nodup_toList _)).mpr
  intro x
  simp only [List.mem_ofFn,Finset.mem_toList,Finset.mem_univ,iff_true]
  exact ⟨e x,e.symm_apply_apply x⟩

variable (G H : Graph) (k : ℕ)

def leftEntries : List (Entry G H k) := List.ofFn fun p : Fin (G.order^k) =>
  Sum.inl (finFunctionFinEquiv.symm p)
def rightEntries : List (Entry G H k) := List.ofFn fun p : Fin (H.order^k) =>
  Sum.inr (finFunctionFinEquiv.symm p)

 theorem leftEntries_address : (leftEntries G H k).map (address G H k)=List.range (G.order^k) := by
  rw [leftEntries,List.map_ofFn,←List.map_coe_finRange_eq_range,←List.ofFn_eq_map]
  congr 1
  funext p
  change (finFunctionFinEquiv (finFunctionFinEquiv.symm p)).val=p.val
  rw [Equiv.apply_symm_apply]

 theorem rightEntries_address : (rightEntries G H k).map (address G H k)=
    (List.range (H.order^k)).map (G.order^k+·) := by
  rw [rightEntries,List.map_ofFn,←ofFn_nat]
  congr 1
  funext p
  change G.order^k+(finFunctionFinEquiv (finFunctionFinEquiv.symm p)).val=G.order^k+p.val
  rw [Equiv.apply_symm_apply]

 theorem leftEntries_perm : (leftEntries G H k).Perm
    ((Finset.univ : Finset (Tuple G k)).toList.map Sum.inl) := by
  have h := (ofFn_perm_univ (finFunctionFinEquiv : Tuple G k ≃ Fin (G.order^k))).map
    (Sum.inl : Tuple G k → Entry G H k)
  simpa only [List.map_ofFn,leftEntries,Function.comp_def] using h

 theorem rightEntries_perm : (rightEntries G H k).Perm
    ((Finset.univ : Finset (Tuple H k)).toList.map Sum.inr) := by
  have h := (ofFn_perm_univ (finFunctionFinEquiv : Tuple H k ≃ Fin (H.order^k))).map
    (Sum.inr : Tuple H k → Entry G H k)
  simpa only [List.map_ofFn,rightEntries,Function.comp_def] using h

 theorem histogram_correct (R : Word) : (data G H k).histogram R=
    histogramEqual G H k (RefinementArray.lookup G H k R) := by
  change sameCounts ((data G H k).get R) (List.range (G.order^k))
    ((List.range (H.order^k)).map (G.order^k+·))=_
  rw [←leftEntries_address G H k,←rightEntries_address G H k,sameCounts_map]
  change sameCounts (RefinementArray.lookup G H k R) (leftEntries G H k) (rightEntries G H k)=_
  exact sameCounts_perm _ (leftEntries_perm G H k) (rightEntries_perm G H k)

 theorem accepts_correct : (data G H k).accepts=true ↔ Equivalent G H k := by
  rw [Data.accepts,histogram_correct,array_correct]
  exact RefinementArray.accepts_correct G H k

end VariableWL.NumericRefinement

end OAI

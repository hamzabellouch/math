import OAI.Combinatorics.VariableWL.RefinementTable

namespace OAI

namespace VariableWL.Encoding
attribute [local instance] Classical.propDecidable

def entry (n : ℕ) (v : Word) (i j : Fin n) : Bool := v.getD (i.val*n+j.val) false

def MatrixValid (n : ℕ) (v : Word) : Prop :=
  v.length=n*n ∧ (∀ i j : Fin n, entry n v i j=entry n v j i) ∧
    (∀ i : Fin n, entry n v i i=false)

def fromMatrix (n : ℕ) (v : Word) (h : MatrixValid n v) : Graph where
  order := n
  graph := {
    Adj := fun i j => entry n v i j=true
    symm := ⟨fun {i j} hij => (h.2.1 j i).trans hij⟩
    loopless := ⟨fun i hi => by have hf := h.2.2 i; rw [hf] at hi; contradiction⟩ }

 theorem entry_matrix (G : Graph) (i j : Fin G.order) :
    entry G.order (matrix G) i j=decide (G.graph.Adj i j) := by
  classical
  have hn : 0<G.order := Nat.zero_lt_of_lt i.isLt
  have hp : i.val*G.order+j.val<G.order*G.order := by
    have := Nat.mul_le_mul_right G.order (Nat.succ_le_of_lt i.isLt)
    nlinarith [j.isLt]
  unfold entry matrix
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hp),List.getElem_ofFn]
  have hd : (⟨i.val*G.order+j.val,hp⟩ : Fin (G.order*G.order)).divNat=i := by
    apply Fin.ext
    simp [Fin.divNat,Nat.add_div,Nat.div_eq_of_lt j.isLt,hn,Nat.mod_lt _ hn]
  have hm : (⟨i.val*G.order+j.val,hp⟩ : Fin (G.order*G.order)).modNat=j := by
    apply Fin.ext
    simp [Fin.modNat,Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  rw [hd,hm]

 theorem matrix_valid (G : Graph) : MatrixValid G.order (matrix G) := by
  refine ⟨matrix_length G,?_,?_⟩
  · intro i j
    rw [entry_matrix,entry_matrix]
    exact decide_eq_decide.mpr (G.graph.adj_comm i j)
  · intro i
    rw [entry_matrix]
    simp

 theorem fromMatrix_matrix (G : Graph) : fromMatrix G.order (matrix G) (matrix_valid G)=G := by
  rcases G with ⟨n,g⟩
  have hg : (fromMatrix n (matrix ⟨n,g⟩) (matrix_valid ⟨n,g⟩)).graph=g := by
    apply SimpleGraph.ext
    change (fun i j : Fin n => entry n (matrix ⟨n,g⟩) i j=true)=g.Adj
    funext i j
    apply propext
    rw [entry_matrix ⟨n,g⟩,decide_eq_true_eq]
  exact congrArg (Graph.mk n) hg

 theorem matrix_fromMatrix (n : ℕ) (v : Word) (h : MatrixValid n v) :
    matrix (fromMatrix n v h)=v := by
  unfold matrix
  change List.ofFn (fun p : Fin (n*n) => @decide (entry n v p.divNat p.modNat=true) (Classical.propDecidable _))=v
  have hd (b : Bool) : @decide (b=true) (Classical.propDecidable _)=b := by
    cases b <;> simp
  simp only [hd]
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using h.1.symm
  · intro a ha hb
    have hp : a<n*n := by simpa only [List.length_ofFn] using ha
    rw [List.getElem_ofFn]
    simp only [entry,Fin.divNat,Fin.modNat]
    rw [Nat.mul_comm (a/n) n,Nat.div_add_mod a n,List.getD_eq_getElem v false hb]

noncomputable def readMatrix (n : ℕ) (v : Word) : Option Graph :=
  if h : MatrixValid n v then some (fromMatrix n v h) else none

 theorem readMatrix_matrix (G : Graph) : readMatrix G.order (matrix G)=some G := by
  simp only [readMatrix,dite_eq_left (matrix_valid G),fromMatrix_matrix]

 theorem readMatrix_sound {n : ℕ} {v : Word} {G : Graph} (h : readMatrix n v=some G) :
    G.order=n ∧ matrix G=v := by
  unfold readMatrix at h
  split_ifs at h with hv
  · cases Option.some.inj h
    exact ⟨rfl,matrix_fromMatrix n v hv⟩

noncomputable def graph (w : Word) : Option (Graph × Word) :=
  match integer w with
  | none => none
  | some (n,u) => (readMatrix n (u.take (n*n))).map fun G => (G,u.drop (n*n))

 theorem graph_code (G : Graph) (v : Word) : graph (graphCode G++v)=some (G,v) := by
  rw [graphCode_eq,List.append_assoc]
  unfold graph
  simp only [integer_code]
  have he := matrix_length G
  rw [← he,List.take_left,readMatrix_matrix,List.drop_left]
  rfl

 theorem graph_sound {w v : Word} {G : Graph} (h : graph w=some (G,v)) : w=graphCode G++v := by
  unfold graph at h
  cases hi : integer w with
  | none => simp [hi] at h
  | some q =>
    rcases q with ⟨n,u⟩
    simp only [hi,Option.map_eq_some_iff] at h
    obtain ⟨G',hg,he⟩ := h
    cases he
    obtain ⟨hn,hm⟩ := readMatrix_sound hg
    rw [integer_sound hi,graphCode_eq,hn,hm,List.append_assoc,List.take_append_drop]

noncomputable def pair (w : Word) : Option (Graph × Graph × ℕ) :=
  match graph w with
  | none => none
  | some (G,u) => match graph u with
    | none => none
    | some (H,v) => match integer v with
      | none => none
      | some (k,t) => if t=[] then some (G,H,k) else none

 theorem pair_code (G H : Graph) (k : ℕ) : pair (pairCode G H k)=some (G,H,k) := by
  unfold pairCode
  rw [List.append_assoc]
  unfold pair
  simp only [graph_code]
  have hi := integer_code k []
  simp only [List.append_nil] at hi
  simp [hi]

 theorem pair_sound {w : Word} {G H : Graph} {k : ℕ} (h : pair w=some (G,H,k)) : w=pairCode G H k := by
  unfold pair at h
  cases hg : graph w with
  | none => simp [hg] at h
  | some p =>
    rcases p with ⟨G',u⟩
    simp only [hg] at h
    cases hh : graph u with
    | none => simp [hh] at h
    | some q =>
      rcases q with ⟨H',v⟩
      simp only [hh] at h
      cases hi : integer v with
      | none => simp [hi] at h
      | some z =>
        rcases z with ⟨k',t⟩
        simp only [hi] at h
        split_ifs at h with ht
        · cases ht
          simp only [Option.some.injEq,Prod.mk.injEq] at h
          rcases h with ⟨rfl,rfl,rfl⟩
          rw [graph_sound hg,graph_sound hh,integer_sound hi,List.append_nil]
          exact List.append_assoc _ _ _ |>.symm

 theorem pair_eq_some_iff {w : Word} {G H : Graph} {k : ℕ} :
    pair w=some (G,H,k) ↔ w=pairCode G H k := ⟨pair_sound,fun h => h ▸ pair_code G H k⟩

 theorem malformed_not_WL {w : Word} (h : pair w=none) : w ∉ WL := by
  rintro ⟨G,H,k,rfl,_⟩
  rw [pair_code] at h
  cases h

 theorem malformed_not_SubWL {w : Word} (h : pair w=none) : w ∉ SubWL := by
  rintro ⟨G,H,k,rfl,_⟩
  rw [pair_code] at h
  cases h

end VariableWL.Encoding

namespace VariableWL.RefinementArray
open RefinementTable
variable (G H : Graph) (k : ℕ)

def count : ℕ := G.order^k+H.order^k

def numbering : Entry G H k ≃ Fin (count G H k) :=
  (Equiv.sumCongr finFunctionFinEquiv finFunctionFinEquiv).trans finSumFinEquiv

def pack (R : Entry G H k → Entry G H k → Bool) : Word :=
  List.ofFn fun p : Fin (count G H k*count G H k) =>
    R ((numbering G H k).symm p.divNat) ((numbering G H k).symm p.modNat)

def lookup (w : Word) (x y : Entry G H k) : Bool :=
  w.getD ((numbering G H k x).val*count G H k+(numbering G H k y).val) false

 theorem lookup_pack (R : Entry G H k → Entry G H k → Bool) (x y : Entry G H k) :
    lookup G H k (pack G H k R) x y=R x y := by
  let a := numbering G H k x
  let b := numbering G H k y
  have hn : 0<count G H k := Nat.zero_lt_of_lt a.isLt
  have hp : a.val*count G H k+b.val<count G H k*count G H k := by
    have := Nat.mul_le_mul_right (count G H k) (Nat.succ_le_of_lt a.isLt)
    nlinarith [b.isLt]
  unfold lookup pack
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hp),List.getElem_ofFn]
  have hd : (⟨a.val*count G H k+b.val,hp⟩ : Fin (count G H k*count G H k)).divNat=a := by
    apply Fin.ext
    simp [Fin.divNat,Nat.add_div,Nat.div_eq_of_lt b.isLt,hn,Nat.mod_lt _ hn]
  have hm : (⟨a.val*count G H k+b.val,hp⟩ : Fin (count G H k*count G H k)).modNat=b := by
    apply Fin.ext
    simp [Fin.modNat,Nat.add_mod,Nat.mod_eq_of_lt b.isLt]
  rw [hd,hm]
  exact congrArg₂ R ((numbering G H k).symm_apply_apply x) ((numbering G H k).symm_apply_apply y)

 theorem pack_length (R : Entry G H k → Entry G H k → Bool) :
    (pack G H k R).length=(count G H k)^2 := by simp only [pack,List.length_ofFn,pow_two]

noncomputable def array : ℕ → Word
  | 0 => pack G H k (RefinementTable.initial G H k)
  | s+1 => pack G H k (update G H k (lookup G H k (array s)))

 theorem array_length (s : ℕ) : (array G H k s).length=(count G H k)^2 := by
  cases s <;> apply pack_length

 theorem array_correct (s : ℕ) (x y : Entry G H k) :
    lookup G H k (array G H k s) x y=table G H k s x y := by
  induction s generalizing x y with
  | zero => exact lookup_pack G H k _ x y
  | succ s ih =>
    rw [array,lookup_pack]
    have he : lookup G H k (array G H k s)=table G H k s := funext fun a => funext fun b => ih a b
    rw [he]
    rfl

noncomputable def accepts : Bool :=
  histogramEqual G H k (lookup G H k (array G H k ((count G H k)^2)))

 theorem accepts_correct : accepts G H k=true ↔ Equivalent G H k := by
  have he : lookup G H k (array G H k ((count G H k)^2))=table G H k ((G.order^k+H.order^k)^2) :=
    funext fun a => funext fun b => array_correct G H k _ a b
  rw [accepts,he]
  exact RefinementTable.accepts_correct G H k

end VariableWL.RefinementArray

namespace VariableWL.InputDecision

def capped (G : Graph) (k : ℕ) : ℕ := min k (max 2 G.order)

 theorem capped_pos (G : Graph) {k : ℕ} (hk : 2≤k) : 0<capped G k := by
  unfold capped
  omega

 theorem equivalent_capped (G H : Graph) {k : ℕ} (hk : 2≤k) :
    Equivalent G H k ↔ Equivalent G H (capped G k) := by
  by_cases h : k ≤ max 2 G.order
  · have he : capped G k=k := Nat.min_eq_left h
    rw [he]
  · have hn : G.order≤k := by omega
    have hc : capped G k=max 2 G.order := Nat.min_eq_right (by omega)
    rw [equivalent_large_iff_iso (by omega) hn,hc,
      equivalent_large_iff_iso (by omega) (le_max_right 2 G.order)]

noncomputable def general (w : Word) : Bool :=
  match Encoding.pair w with
  | none => false
  | some (G,H,k) => decide (2≤k) && RefinementArray.accepts G H (capped G k)

 theorem general_correct (w : Word) : general w=true ↔ w ∈ WL := by
  unfold general
  cases hp : Encoding.pair w with
  | none => simp only [Bool.false_eq_true,false_iff]; exact Encoding.malformed_not_WL hp
  | some q =>
    rcases q with ⟨G,H,k⟩
    have hw := Encoding.pair_sound hp
    rw [hw,Encoding.pair_mem_WL,Bool.and_eq_true,decide_eq_true_eq,RefinementArray.accepts_correct]
    exact and_congr_right fun hk => (equivalent_capped G H hk).symm

end VariableWL.InputDecision

namespace VariableWL.PromiseDecision
attribute [local instance] Classical.propDecidable
variable (G : Graph)

noncomputable def reach : ℕ → Fin G.order → Fin G.order → Bool
  | 0,u,v => decide (u=v)
  | t+1,u,v => reach t u v || (List.finRange G.order).any fun z =>
      decide (G.graph.Adj u z) && reach t z v

 theorem reach_correct (t : ℕ) (u v : Fin G.order) :
    reach G t u v=true ↔ ∃ p : G.graph.Walk u v, p.length≤t := by
  induction t generalizing u v with
  | zero =>
    simp only [reach,decide_eq_true_eq,Nat.le_zero]
    constructor
    · rintro rfl; exact ⟨.nil,rfl⟩
    · rintro ⟨p,hp⟩
      cases p with
      | nil => rfl
      | cons h p => simp at hp
  | succ t ih =>
    simp only [reach,Bool.or_eq_true,List.any_eq_true,List.mem_finRange,true_and,
      Bool.and_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro (⟨p,hp⟩|⟨z,huz,p,hp⟩)
      · exact ⟨p,Nat.le_succ_of_le hp⟩
      · exact ⟨.cons huz p,Nat.succ_le_succ hp⟩
    · rintro ⟨p,hp⟩
      cases p with
      | nil => exact .inl ⟨.nil,Nat.zero_le _⟩
      | @cons z x y hu p => exact .inr ⟨x,hu,p,Nat.le_of_succ_le_succ hp⟩

 theorem reach_order (u v : Fin G.order) : reach G G.order u v=true ↔ G.graph.Reachable u v := by
  rw [reach_correct]
  constructor
  · rintro ⟨p,_⟩; exact p.reachable
  · intro h
    obtain ⟨p,hp⟩ := h.exists_isPath
    exact ⟨p,by have hh := hp.length_lt; simpa only [Fintype.card_fin] using hh.le⟩

noncomputable def connected : Bool := decide (0<G.order) &&
  (List.finRange G.order).all fun u => (List.finRange G.order).all fun v => reach G G.order u v

 theorem connected_correct : connected G=true ↔ G.graph.Connected := by
  simp only [connected,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_finRange,
    forall_const,reach_order]
  constructor
  · rintro ⟨hn,hr⟩
    let : Nonempty (Fin G.order) := ⟨⟨0,hn⟩⟩
    exact ⟨hr⟩
  · intro h
    exact ⟨by have := h.nonempty; exact Fin.pos_iff_nonempty.mpr this,h.preconnected⟩

noncomputable def neighbors (u : Fin G.order) : List (Fin G.order) :=
  (List.finRange G.order).filter fun v => decide (G.graph.Adj u v)

 theorem neighbors_length (u : Fin G.order) : (neighbors G u).length=G.graph.degree u := by
  classical
  have hn : (neighbors G u).Nodup := (List.nodup_finRange _).filter _
  have he : (neighbors G u).toFinset=G.graph.neighborFinset u := by
    ext v
    simp [neighbors]
  rw [← List.toFinset_card_of_nodup hn,he]
  rfl

noncomputable def subcubic : Bool := (List.finRange G.order).all fun u => decide ((neighbors G u).length≤3)

 theorem subcubic_correct : subcubic G=true ↔ Subcubic G := by
  simp only [subcubic,List.all_eq_true,List.mem_finRange,forall_const,decide_eq_true_eq,neighbors_length]
  rfl

end VariableWL.PromiseDecision

namespace VariableWL.InputDecision

noncomputable def subcubic (w : Word) : Bool :=
  match Encoding.pair w with
  | none => false
  | some (G,H,k) => decide (2≤k) && decide (0<G.order) && decide (G.order=H.order) &&
    PromiseDecision.connected G && PromiseDecision.connected H &&
    PromiseDecision.subcubic G && PromiseDecision.subcubic H &&
    RefinementArray.accepts G H (capped G k)

 theorem subcubic_correct (w : Word) : subcubic w=true ↔ w ∈ SubWL := by
  unfold subcubic
  cases hp : Encoding.pair w with
  | none => simp only [Bool.false_eq_true,false_iff]; exact Encoding.malformed_not_SubWL hp
  | some q =>
    rcases q with ⟨G,H,k⟩
    have hw := Encoding.pair_sound hp
    rw [hw,Encoding.pair_mem_SubWL]
    simp only [Bool.and_eq_true,decide_eq_true_eq,PromiseDecision.connected_correct,
      PromiseDecision.subcubic_correct,RefinementArray.accepts_correct]
    rw [and_assoc,and_assoc,and_assoc,and_assoc,and_assoc,and_assoc]
    exact and_congr_right fun hk => by rw [equivalent_capped G H hk]

end VariableWL.InputDecision

end OAI

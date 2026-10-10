import Mathlib
import OAI.Computability.QuantumFactoring.NativeAIGFullAdder

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open BitStackProgram BitStackProgram.Procedure

def DeclBound (B : ℕ) : Decl→Prop
  | .zero=>True
  | .atom i=>i≤B
  | .gate a b=>a.1≤B ∧ b.1≤B
structure Bounded (B : ℕ) (r : Graph) : Prop where
  decl_length : r.decls.length≤B
  cache_length : r.cache.length≤B
  decls : ∀d∈r.decls,DeclBound B d
  cache : ∀e∈r.cache,e.1.1.1≤B ∧ e.1.2.1≤B ∧ e.2≤B
lemma DeclBound.mono {A B : ℕ} (h : A≤B) {d : Decl} (hd : DeclBound A d) : DeclBound B d := by
  cases d <;> simp only [DeclBound] at * <;> omega
lemma Bounded.mono {A B : ℕ} {r : Graph} (h : A≤B) (hr : Bounded A r) : Bounded B r :=
  ⟨hr.decl_length.trans h,hr.cache_length.trans h,fun d hd=>(hr.decls d hd).mono h,
    fun e he=>by have hh:=hr.cache e he;omega⟩
lemma lookup_bound {B : ℕ} {es : List (Key×ℕ)}
    (h : ∀e∈es,e.2≤B) (k : Key) {v : ℕ} (hv : lookup k es=some v) : v≤B := by
  induction es with
  | nil=>simp [lookup] at hv
  | cons e es ih=>
    simp only [lookup] at hv
    split_ifs at hv with he
    · cases hv;exact h e (by simp)
    · exact ih (fun a ha=>h a (by simp [ha])) hv
lemma addGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (addGate r a b).1 ∧ (addGate r a b).2.1≤B+1 := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · simp only [addGate,List.length_append,List.length_cons,List.length_nil];have:=h.decl_length;omega
  · simp only [addGate,List.length_cons];have:=h.cache_length;omega
  · intro d hd
    simp only [addGate,List.mem_append,List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact (h.decls d hd).mono (by omega)
    · simp only [DeclBound];omega
  · intro e he
    simp only [addGate,List.mem_cons] at he
    rcases he with rfl | he
    · dsimp only;have:=h.decl_length;omega
    · have:=h.cache e he;omega
  · exact h.decl_length.trans (by omega)
lemma go_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (go r a b).1 ∧ (go r a b).2.1≤B+1 := by
  have hg:=h.mono (Nat.le_add_right B 1)
  unfold go
  cases hl : lookup (a,b) r.cache with
  | some v=>
    dsimp only
    have hv:=lookup_bound (fun e he=>(h.cache e he).2.2) (a,b) hl
    exact ⟨hg,by omega⟩
  | none=>
    dsimp only
    cases hc : constant r a with
    | some a'=>
      cases a' <;> cases hd : constant r b with
      | none=>dsimp only;exact ⟨hg,by omega⟩
      | some b'=>cases b' <;> dsimp only <;> exact ⟨hg,by omega⟩
    | none=>
      cases hd : constant r b with
      | some b'=>cases b' <;> dsimp only <;> exact ⟨hg,by omega⟩
      | none=>
        dsimp only
        split_ifs
        · exact ⟨hg,ha.trans (by omega)⟩
        · exact ⟨hg,Nat.zero_le _⟩
        · exact addGate_bound h a b ha hb
lemma gate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (gate r a b).1 ∧ (gate r a b).2.1≤B+1 := by
  unfold gate;split <;> exact go_bound h _ _ (by omega) (by omega)
lemma orGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+1) (orGate r a b).1 ∧ (orGate r a b).2.1≤B+1 :=
  gate_bound h (notRef a) (notRef b) ha hb
lemma xorGate_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b : Ref)
    (ha : a.1≤B) (hb : b.1≤B) :
    Bounded (B+3) (xorGate r a b).1 ∧ (xorGate r a b).2.1≤B+3 := by
  have hs:=gate_bound h a b ha hb
  have ht:=gate_bound hs.1 (notRef a) (notRef b) (by exact ha.trans (by omega)) (by exact hb.trans (by omega))
  have hh:=gate_bound ht.1 (notRef (gate r a b).2)
    (notRef (gate (gate r a b).1 (notRef a) (notRef b)).2) (by exact hs.2.trans (by omega)) ht.2
  exact hh
lemma fullOut_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b c : Ref)
    (ha : a.1≤B) (hb : b.1≤B) (hc : c.1≤B) :
    Bounded (B+6) (fullOut r a b c).1 ∧ (fullOut r a b c).2.1≤B+6 := by
  have hs:=xorGate_bound h a b ha hb
  exact xorGate_bound hs.1 _ c hs.2 (hc.trans (by omega))
lemma fullCarry_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b c : Ref)
    (ha : a.1≤B) (hb : b.1≤B) (hc : c.1≤B) :
    Bounded (B+6) (fullCarry r a b c).1 ∧ (fullCarry r a b c).2.1≤B+6 := by
  have hs:=xorGate_bound h a b ha hb
  have ht:=gate_bound hs.1 _ c hs.2 (hc.trans (by omega))
  have hu:=gate_bound ht.1 a b (ha.trans (by omega)) (hb.trans (by omega))
  exact orGate_bound hu.1 _ _ (ht.2.trans (by omega)) hu.2
lemma full_bound {B : ℕ} {r : Graph} (h : Bounded B r) (a b c : Ref)
    (ha : a.1≤B) (hb : b.1≤B) (hc : c.1≤B) :
    Bounded (B+12) (full r a b c).1 ∧
      (full r a b c).2.1.1≤B+12 ∧ (full r a b c).2.2.1≤B+12 := by
  have ho:=fullOut_bound h a b c ha hb hc
  have hk:=fullCarry_bound ho.1 a b c (ha.trans (by omega)) (hb.trans (by omega)) (hc.trans (by omega))
  exact ⟨hk.1,ho.2.trans (by omega),hk.2⟩
lemma nat_bits_length_bound (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self
lemma refCode_length_bound {B : ℕ} (a : Ref) (ha : a.1≤B) : (refCode a).length≤2*B+2 := by
  have hn:=nat_bits_length_bound a.1
  simp only [refCode,prodCode,pairBits_length,boolCode,List.length_singleton]
  omega
lemma keyCode_length_bound {B : ℕ} (k : Key) (ha : k.1.1≤B) (hb : k.2.1≤B) :
    (keyCode k).length≤6*B+7 := by
  have h1:=refCode_length_bound k.1 ha
  have h2:=refCode_length_bound k.2 hb
  change (pairBits (refCode k.1) (refCode k.2)).length≤_
  rw [pairBits_length]
  omega
lemma declCode_length_bound {B : ℕ} (d : Decl) (hd : DeclBound B d) :
    (declCode d).length≤6*B+9 := by
  cases d with
  | zero=>simp [declCode,declView,sumCode,emptyCode]
  | atom i=>
    have hh:=nat_bits_length_bound i
    simp only [DeclBound] at hd
    simp only [declCode,declView,sumCode,List.length_cons];omega
  | gate a b=>
    have hh:=keyCode_length_bound (a,b) hd.1 hd.2
    simp only [declCode,declView,sumCode,List.length_cons];omega
lemma entryCode_length_bound {B : ℕ} (e : Key×ℕ) (h : e.1.1.1≤B ∧ e.1.2.1≤B ∧ e.2≤B) :
    (entryCode e).length≤13*B+15 := by
  have hk:=keyCode_length_bound e.1 h.1 h.2.1
  have hn:=nat_bits_length_bound e.2
  change (pairBits (keyCode e.1) e.2.bits).length≤_
  rw [pairBits_length]
  omega
lemma listCode_length_bound {α : Type} (e : α→List Bool) (xs : List α) (B : ℕ)
    (h : ∀x∈xs,(e x).length≤B) : (listCode e xs).length≤xs.length*(2*B+2)+1 := by
  simpa only [List.map_id] using listCode_length_map_bound e id xs B h
lemma graphCode_length_bound {B : ℕ} {r : Graph} (h : Bounded B r) :
    (graphCode r).length≤100*(B+1)^2 := by
  have hd:=listCode_length_bound declCode r.decls (6*B+9)
    (fun d hd=>declCode_length_bound d (h.decls d hd))
  have hc:=listCode_length_bound entryCode r.cache (13*B+15)
    (fun e he=>entryCode_length_bound e (h.cache e he))
  have hdm:=Nat.mul_le_mul_right (2*(6*B+9)+2) h.decl_length
  have hcm:=Nat.mul_le_mul_right (2*(13*B+15)+2) h.cache_length
  change (pairBits (listCode declCode r.decls) (listCode entryCode r.cache)).length≤_
  rw [pairBits_length]
  nlinarith
end ExactQuantumFactoring.NativeAIG

end



end OAI

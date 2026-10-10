import Mathlib

namespace OAI



section

namespace ExactQuantumFactoring.NativeAIG
open Std Sat
abbrev Ref := ℕ × Bool
abbrev Key := Ref × Ref
/-- A literal list representation of the nodes and the (possibly incomplete)
cache. The cache is not replaced by a search through all nodes. -/
inductive Decl where
  | zero
  | atom (i : ℕ)
  | gate (a b : Ref)
  deriving DecidableEq, Inhabited
structure Graph where
  decls : List Decl
  cache : List (Key × ℕ)
  deriving Inhabited

def eraseDecl {n : ℕ} : AIG.Decl (Fin n) → Decl
  | .false => .zero
  | .atom i => .atom i.val
  | .gate a b => .gate (a.gate,a.invert) (b.gate,b.invert)
def lookup (k : Key) : List (Key × ℕ) → Option ℕ
  | [] => none
  | (a,v)::as => if k=a then some v else lookup k as

def nativeKey {n : ℕ} (k : Key) : AIG.Decl (Fin n) :=
  .gate (.mk k.1.1 k.1.2) (.mk k.2.1 k.2.2)
def Rel {n : ℕ} (r : Graph) (g : AIG (Fin n)) : Prop :=
  r.decls=g.decls.toList.map eraseDecl ∧
  ∀ k,lookup k r.cache=g.cache.val[nativeKey (n:=n) k]?
def constant (r : Graph) (a : Ref) : Option Bool :=
  match r.decls[a.1]?.getD .zero with
  | .zero => some a.2
  | _ => none

def empty : Graph := ⟨[.zero],[]⟩
def atom (r : Graph) (i : ℕ) : Graph × Ref :=
  (⟨r.decls++[.atom i],r.cache⟩,(r.decls.length,false))
def addGate (r : Graph) (a b : Ref) : Graph × Ref :=
  (⟨r.decls++[.gate a b],((a,b),r.decls.length)::r.cache⟩,(r.decls.length,false))
def go (r : Graph) (a b : Ref) : Graph × Ref :=
  match lookup (a,b) r.cache with
  | some i => (r,(i,false))
  | none =>
    match constant r a,constant r b with
    | some false,_ | _,some false => (r,(0,false))
    | some true,_ => (r,b)
    | _,some true => (r,a)
    | _,_ => if a.1=b.1 then
        if a.2=b.2 then (r,a) else (r,(0,false))
      else addGate r a b
def gate (r : Graph) (a b : Ref) : Graph × Ref :=
  if a.1<b.1 then go r a b else go r b a

def EPRel {n : ℕ} (r : Graph × Ref) (e : AIG.Entrypoint (Fin n)) : Prop :=
  Rel r.1 e.aig ∧ r.2=(e.ref.gate,e.ref.invert)

lemma cache_project {α : Type} [Hashable α] [DecidableEq α]
    {ds : Array (AIG.Decl α)} (c : AIG.Cache α ds) (d : AIG.Decl α) :
    (c.get? d).map AIG.CacheHit.idx=c.val[d]? := by
  unfold AIG.Cache.get?
  split <;> simp_all
lemma nativeKey_injective {n : ℕ} : Function.Injective (nativeKey (n:=n)) := by
  rintro ⟨⟨a,ai⟩,⟨b,bi⟩⟩ ⟨⟨c,ci⟩,⟨d,di⟩⟩ h
  simp only [nativeKey,AIG.Decl.gate.injEq] at h
  have ha:=congrArg AIG.Fanin.gate h.1
  have hai:=congrArg AIG.Fanin.invert h.1
  have hb:=congrArg AIG.Fanin.gate h.2
  have hbi:=congrArg AIG.Fanin.invert h.2
  simp only [AIG.Fanin.gate_mk,AIG.Fanin.invert_mk] at *
  simp_all
lemma empty_rel (n : ℕ) : Rel empty (AIG.empty : AIG (Fin n)) := by
  constructor
  · rfl
  · intro k;simp [empty,lookup,AIG.empty,AIG.Cache.empty]
lemma constant_eq {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (a : AIG.Ref g) :
    constant r (a.gate,a.invert)=AIG.getConstant g a := by
  unfold constant
  rw [h.1]
  simp only [List.getElem?_map,Array.getElem?_toList,Array.getElem?_eq_getElem a.hgate,Option.map_some,
    Option.getD_some]
  rw [AIG.getConstant]
  cases g.decls[a.gate]'a.hgate <;> rfl
lemma atom_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : Fin n) :
    EPRel (atom r i.val) (AIG.mkAtom g i) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · simpa only [atom,AIG.mkAtom,Array.toList_push,List.map_append,List.map_cons,List.map_nil,eraseDecl]
      using congrArg (fun ds=>ds++[Decl.atom i.val]) h.1
  · intro k;simpa only [atom,AIG.mkAtom,AIG.Cache.noUpdate] using h.2 k
  · simp only [atom,AIG.mkAtom,h.1,List.length_map,Array.length_toList]
lemma pushed_rel {n : ℕ} {r : Graph} {g g' : AIG (Fin n)} (h : Rel r g) (a b : Ref)
    (hd : g'.decls=g.decls.push (nativeKey (a,b)))
    (hc : g'.cache.val=g.cache.val.insert (nativeKey (a,b)) g.decls.size) :
    Rel (addGate r a b).1 g' := by
  constructor
  · simp only [addGate,hd,Array.toList_push,List.map_append,List.map_cons,List.map_nil,
      nativeKey,eraseDecl,AIG.Fanin.gate_mk,AIG.Fanin.invert_mk,h.1]
  · intro k
    simp only [addGate,lookup,hc,Std.HashMap.getElem?_insert]
    simp only [beq_iff_eq,(nativeKey_injective (n:=n)).eq_iff]
    by_cases hk:k=(a,b)
    · simp only [hk,↓reduceIte,h.1,List.length_map,Array.length_toList]
    · simp only [hk,Ne.symm hk,↓reduceIte,h.2]

lemma go_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (go r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (AIG.mkGateCached.go g i) := by
  let k : Key:=((i.lhs.gate,i.lhs.invert),(i.rhs.gate,i.rhs.invert))
  have hl : lookup k r.cache=(g.cache.get? (nativeKey k)).map AIG.CacheHit.idx :=
    (h.2 k).trans (cache_project _ _).symm
  unfold go AIG.mkGateCached.go
  dsimp only
  change EPRel (match lookup k r.cache with
    | some v => (r,(v,false))
    | none => _) _
  rw [hl]
  cases hc : g.cache.get? (nativeKey k) with
  | some hit =>
    simp only [Option.map_some]
    simp only [nativeKey,k] at hc
    simp only [hc]
    exact ⟨h,rfl⟩
  | none =>
    simp only [Option.map_none]
    simp only [nativeKey,k] at hc
    simp only [hc]
    rw [constant_eq h i.lhs,constant_eq h i.rhs]
    cases ha : AIG.getConstant g i.lhs with
    | some a =>
      cases a <;> cases hb : AIG.getConstant g i.rhs with
      | none => exact ⟨h,rfl⟩
      | some b => cases b <;> exact ⟨h,rfl⟩
    | none =>
      cases hb : AIG.getConstant g i.rhs with
      | some b => cases b <;> exact ⟨h,rfl⟩
      | none =>
        simp only [beq_iff_eq]
        by_cases he : i.lhs.gate=i.rhs.gate
        · simp only [he,↓reduceIte]
          by_cases hi : i.lhs.invert=i.rhs.invert <;>
            simp only [hi,↓reduceIte] <;> exact ⟨h,rfl⟩
        · simp only [he,↓reduceIte]
          refine ⟨pushed_rel h _ _ rfl ?_,?_⟩
          · simp only [AIG.Cache.insert];rfl
          · simp only [addGate,h.1,List.length_map,Array.length_toList]
lemma gate_rel {n : ℕ} {r : Graph} {g : AIG (Fin n)} (h : Rel r g) (i : AIG.BinaryInput g) :
    EPRel (gate r (i.lhs.gate,i.lhs.invert) (i.rhs.gate,i.rhs.invert))
      (g.mkGateCached i) := by
  unfold gate AIG.mkGateCached
  dsimp only
  split
  · exact go_rel h ⟨i.lhs,i.rhs⟩
  · exact go_rel h ⟨i.rhs,i.lhs⟩
end ExactQuantumFactoring.NativeAIG

end



end OAI

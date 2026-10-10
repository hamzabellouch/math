import Mathlib
import OAI.Combinatorics.UniformKServer.Basic

namespace OAI

noncomputable section
                                
section

/-! A stack is physically stored at a tape head. Padding is literal blank
cells, not a unit-cost unbounded register. Each push/pop uses at most two
transitions. -/
namespace UniformKServer.StackTape

def encode (s : List Bool) (l r : ℕ) : BitTape :=
  match s with
  | [] => ⟨List.replicate l none,none,List.replicate r none⟩
  | b::bs => ⟨List.replicate l none,some b,bs.map some ++ List.replicate r none⟩

def Rep (s : List Bool) (t : BitTape) : Prop := ∃ l r,t=encode s l r

theorem head {s : List Bool} {t : BitTape} (h : Rep s t) : t.head=s.head? := by
  obtain ⟨l,r,rfl⟩:=h
  cases s <;> rfl

theorem blank : Rep [] BitTape.blank := ⟨0,0,rfl⟩

def push (b : Bool) (t : BitTape) : BitTape :=
  {t.shift .left with head:=some b}

def pop (t : BitTape) : BitTape :=
  if t.head=none then t else ({t with head:=none}).shift .right

theorem push_rep (b : Bool) {s : List Bool} {t : BitTape} (h : Rep s t) :
    Rep (b::s) (push b t) := by
  obtain ⟨l,r,rfl⟩:=h
  cases s with
  | nil =>
    cases l with
    | zero => exact ⟨0,r+1,by simp [push,encode,BitTape.shift,List.replicate_succ]⟩
    | succ l => exact ⟨l,r+1,by simp [push,encode,BitTape.shift,List.replicate_succ]⟩
  | cons a s =>
    cases l with
    | zero => exact ⟨0,r,by simp [push,encode,BitTape.shift]⟩
    | succ l => exact ⟨l,r,by simp [push,encode,BitTape.shift,List.replicate_succ]⟩

theorem pop_rep {s : List Bool} {t : BitTape} (h : Rep s t) : Rep s.tail (pop t) := by
  obtain ⟨l,r,rfl⟩:=h
  cases s with
  | nil => exact ⟨l,r,by simp [pop,encode]⟩
  | cons b s =>
    cases s with
    | nil =>
      cases r with
      | zero => exact ⟨l+1,0,by simp [pop,encode,BitTape.shift,List.replicate_succ]⟩
      | succ r => exact ⟨l+1,r,by simp [pop,encode,BitTape.shift,List.replicate_succ]⟩
    | cons a s => exact ⟨l+1,r,by simp [pop,encode,BitTape.shift,List.replicate_succ]⟩

end UniformKServer.StackTape

end


end

end OAI

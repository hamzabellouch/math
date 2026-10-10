import Mathlib.Data.List.Nodup
import OAI.Analysis.Laughlin.FourBody.Basic

namespace OAI

namespace Laughlin.Certificate

private def quadTail (D a b : ℕ) :=
  (List.range (D+2)).filterMap (fun c =>
    let d := D+1-a-b-c
    if a<b ∧ b<c ∧ c<d ∧ a+b+c≤D+1 then some (a,b,c,d) else none)

private theorem mem_quadTail (D a b x y z w : ℕ) :
    (x,y,z,w) ∈ quadTail D a b ↔
      x=a ∧ y=b ∧ a<b ∧ b<z ∧ z<w ∧ a+b+z+w=D+1 := by
  simp only [quadTail,List.mem_filterMap,List.mem_range]
  constructor
  · rintro ⟨c,hc,he⟩
    split_ifs at he with h
    · simp only [Option.some.injEq,Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl,rfl,rfl⟩
      omega
  · rintro ⟨rfl,rfl,hab,hbz,hzw,hs⟩
    refine ⟨z,by omega,?_⟩
    have hd : D+1-x-y-z=w := by omega
    simp [hd,hab,hbz,hzw,show x+y+z≤D+1 by omega]

theorem mem_quadruples (D a b c d : ℕ) :
    (a,b,c,d) ∈ quadruples D ↔ a<b ∧ b<c ∧ c<d ∧ a+b+c+d=D+1 := by
  change (a,b,c,d) ∈ (List.range (D+2)).flatMap
    (fun x => (List.range (D+2)).flatMap (quadTail D x)) ↔ _
  simp only [List.mem_flatMap,List.mem_range,mem_quadTail]
  constructor
  · rintro ⟨x,hx,y,hy,rfl,rfl,h⟩
    exact h
  · rintro ⟨hab,hbc,hcd,hs⟩
    exact ⟨a,by omega,b,by omega,rfl,rfl,hab,hbc,hcd,hs⟩

private theorem quadTail_nodup (D a b : ℕ) : (quadTail D a b).Nodup := by
  apply List.Nodup.filterMap _ List.nodup_range
  intro c c' t hc hc'
  dsimp only at hc hc'
  split_ifs at hc with h
  · split_ifs at hc' with h'
    · simp only [Option.mem_def,Option.some.injEq] at hc hc'
      have he := hc.trans hc'.symm
      exact congrArg (fun u : ℕ×ℕ×ℕ×ℕ => u.2.2.1) he
    · simp at hc'
  · simp at hc

theorem quadruples_nodup (D : ℕ) : (quadruples D).Nodup := by
  change ((List.range (D+2)).flatMap
    (fun a => (List.range (D+2)).flatMap (quadTail D a))).Nodup
  apply List.nodup_flatMap.mpr
  constructor
  · intro a ha
    apply List.nodup_flatMap.mpr
    constructor
    · intro b hb; exact quadTail_nodup D a b
    · apply List.nodup_range.imp
      intro b b' hne t ht ht'
      obtain ⟨x,y,z,w⟩ := t
      have h := (mem_quadTail D a b x y z w).mp ht
      have h' := (mem_quadTail D a b' x y z w).mp ht'
      exact hne (h.2.1.symm.trans h'.2.1)
  · apply List.nodup_range.imp
    intro a a' hne t ht ht'
    obtain ⟨b,hb,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b',hb',ht'⟩ := List.mem_flatMap.mp ht'
    obtain ⟨x,y,z,w⟩ := t
    have h := (mem_quadTail D a b x y z w).mp ht
    have h' := (mem_quadTail D a' b' x y z w).mp ht'
    exact hne (h.1.symm.trans h'.1)

end Laughlin.Certificate

end OAI

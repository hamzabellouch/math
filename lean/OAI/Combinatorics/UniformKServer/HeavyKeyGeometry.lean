import Mathlib
import OAI.Combinatorics.UniformKServer.LevelMap

namespace OAI

                                       
section

/-! Heavy precedence, disjoint nearby anchors, and the actual inner ball. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}

theorem key_heavy_iff (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (p : X) (l : HeavySlot X) :
    D.key is z t p=Sum.inl l ↔ HeavyRecords.covers (D.heavyState z.1 t) l p := by
  rw [←HeavyRecords.key_some _ D.positive.le p l]
  cases hh : HeavyRecords.key (D.heavyState z.1 t) p with
  | some a => simp only [key,heavyKey,hh,Option.map_some,Option.some_or,Option.getD_some,Sum.inl.injEq,Option.some.injEq]
  | none =>
    simp only [key,heavyKey,hh,Option.map_none,Option.none_or]
    cases ht : FirstStructure.first is (fun i=>D.tierKey z t i p) with
    | none => simp
    | some b =>
      obtain ⟨i,hi,hb⟩ := first_witness is _ b ht
      obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hb
      simp

theorem near_unique (D : LevelMap.Data X N H) (z : Tape D) (t : ℕ)
    (y : X) (a b : HeavySlot X) (ha : a∈(D.heavyState z.1 t).present)
    (hb : b∈(D.heavyState z.1 t).present)
    (hya : dist y ((D.heavyState z.1 t).center a)≤7*D.r)
    (hyb : dist y ((D.heavyState z.1 t).center b)≤7*D.r) : a=b := by
  by_contra hn
  have hs := (D.heavyState z.1 t).separated a ha b hb hn
  have ht := dist_triangle ((D.heavyState z.1 t).center a) y ((D.heavyState z.1 t).center b)
  rw [dist_comm _ y] at ht
  linarith [D.positive]

theorem inner_heavy (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (y p : X) (l : HeavySlot X)
    (hl : l∈(D.heavyState z.1 t).present)
    (hy : dist y ((D.heavyState z.1 t).center l)≤7*D.r) (hp : dist y p≤D.r) :
    D.key is z t p=Sum.inl l := by
  apply (key_heavy_iff D is z t p l).mpr
  refine ⟨hl,?_⟩
  have hr := ((D.heavyState z.1 t).radius_bounds l hl).1
  have ht := dist_triangle ((D.heavyState z.1 t).center l) y p
  rw [dist_comm _ y] at ht
  linarith [D.positive]

end UniformKServer.LevelMap.Data

end


end

end OAI

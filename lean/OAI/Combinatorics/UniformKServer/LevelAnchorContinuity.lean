import Mathlib
import OAI.Combinatorics.UniformKServer.ActualAnchorTravel

namespace OAI

                                            
section

/-! Cross-time witnesses for a literal fixed-alphabet key. Tier labels cannot
be reassigned on consecutive supported maps; only retained heavy labels move. -/
noncomputable section
namespace UniformKServer.LevelMap.Data
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance ixAC (m : ℕ) : DecidableEq (Fin m) := fun a b=>Classical.propDecidable (a=b)
local instance pairAC : DecidableEq (X × X) := fun a b=>Classical.propDecidable (a=b)

theorem key_tier_witness (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (p : X) (i : Fin H) (l : TierLabeledKeys.Slot X (D.K i))
    (hl : D.key is z t p=Sum.inr (Sum.inl ⟨i,l⟩)) :
    TierLabeledKeys.key D.r (D.K i) (D.qualify i) D.center t (z.2 i).1 (z.2 i).2 p=some l := by
  cases hh : D.heavyKey z t p with
  | some a =>
    obtain ⟨h,_,rfl⟩ := Option.map_eq_some_iff.mp hh
    simp only [key,hh,Option.some_or,Option.getD_some] at hl
    cases hl
  | none =>
    cases ht : FirstStructure.first is (fun j=>D.tierKey z t j p) with
    | none => simp [key,hh,ht] at hl
    | some a =>
      have ha : a=Sum.inr (Sum.inl ⟨i,l⟩) := by simpa only [key,hh,Option.none_or,ht,Option.getD_some] using hl
      obtain ⟨j,_,hj⟩ := first_witness is _ a ht
      obtain ⟨m,hm,he⟩ := Option.map_eq_some_iff.mp hj
      have he' : (Sigma.mk j m : (j : Fin H) × TierLabeledKeys.Slot X (D.K j))=⟨i,l⟩ :=
        Sum.inl.inj (Sum.inr.inj (he.trans ha))
      cases he'
      exact hm

theorem supported_transition (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (p q : X) (l : Label D)
    (hp : D.key is z t p=l) (hq : D.key is z (t+1) q=l) :
    D.anchor z t l=D.anchor z (t+1) l ∨
      ∃ a : HeavySlot X,l=Sum.inl a ∧ a∈(D.heavyState z.1 t).present ∧
        a∈(D.heavyState z.1 (t+1)).present := by
  rcases l with a|⟨i,l⟩|x
  · exact Or.inr ⟨a,rfl,((key_heavy_iff D is z t p a).mp hp).1,
      ((key_heavy_iff D is z (t+1) q a).mp hq).1⟩
  · left
    exact TierLabeledKeys.common_anchor D.base D.r D.positive.le (D.K i) (D.two i) (D.quota i)
      (D.qualify i) D.center t (z.2 i).1 (z.2 i).2 p q l
      (key_tier_witness D is z t p i l hp) (key_tier_witness D is z (t+1) q i l hq)
  · exact Or.inl rfl

theorem supported_distance (D : LevelMap.Data X N H) (is : List (Fin H))
    (z : Tape D) (t : ℕ) (p q : X) (l : Label D)
    (hp : D.key is z t p=l) (hq : D.key is z (t+1) q=l) :
    dist (D.anchor z t l) (D.anchor z (t+1) l)≤40*D.r := by
  obtain ha|⟨a,rfl,ho,hn⟩ := supported_transition D is z t p q l hp hq
  · rw [ha,dist_self]
    exact mul_nonneg (by norm_num) D.positive.le
  · by_cases he : (D.heavyState z.1 t).center a=(D.heavyState z.1 (t+1)).center a
    · change dist ((D.heavyState z.1 t).center a) ((D.heavyState z.1 (t+1)).center a)≤_
      rw [he,dist_self]
      exact mul_nonneg (by norm_num) D.positive.le
    · exact anchor_distance D z t a ho hn he

end UniformKServer.LevelMap.Data

end


end

end OAI

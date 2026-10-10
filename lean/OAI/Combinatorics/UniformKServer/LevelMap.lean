import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyTape
import OAI.Combinatorics.UniformKServer.TierLabeledKeys
import OAI.Combinatorics.UniformKServer.FirstStructure

namespace OAI

                               
section

/-! The literal level key: heavy precedence, then chronological tiers in their
fixed order, then singleton fallback. Its alphabet is fixed by the instance,
not by the finite law or horizon used to analyze the independent tape. -/
noncomputable section
namespace UniformKServer.LevelMap
open Finset FiniteProbability
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X] {N H : ℕ}
local instance indexDecEq : DecidableEq (Fin N) := fun a b => Classical.propDecidable (a=b)
local instance tierDecEq : DecidableEq (Fin H) := fun a b => Classical.propDecidable (a=b)
local instance pairDecEq : DecidableEq (X × X) := fun a b => Classical.propDecidable (a=b)

structure Data (X : Type) [Fintype X] [MetricSpace X] (N H : ℕ) where
  r : ℝ
  positive : 0<r
  K : Fin H → ℕ
  two : ∀ i, 2≤K i
  base : X
  center : Fin N → X
  heavy : Fin N → Prop
  qualify : Fin H → Fin N → Prop

abbrev HeavySlot (X : Type) [Fintype X] := Fin (2*Fintype.card X+1)
abbrev Label (D : Data X N H) := HeavySlot X ⊕ ((i : Fin H) × TierLabeledKeys.Slot X (D.K i)) ⊕ X
abbrev HeavyTape (D : Data X N H) := Fin N → HeavyRadius.Sample (X:=X) D.r
abbrev TierTape (D : Data X N H) (i : Fin H) := TierLifetimes.Tape N ×
  (Fin N → TierRadius.Sample (X:=X) (Real.log (1+(D.K i:ℝ)^2)) D.r)
abbrev Tape (D : Data X N H) := HeavyTape D × (∀ i, TierTape D i)

namespace Data

theorem quota (D : Data X N H) (i : Fin H) : 1/(D.K i:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
  have hk : (2:ℝ)≤D.K i := by exact_mod_cast D.two i
  constructor
  · positivity
  · exact (div_le_one (by linarith)).mpr (by linarith)

def point (D : Data X N H) (t : ℕ) : X := if ht : t<N then D.center ⟨t,ht⟩ else D.base
def heavyFlag (D : Data X N H) (t : ℕ) : Prop := ∃ ht : t<N, D.heavy ⟨t,ht⟩

def heavyState (D : Data X N H) (ω : HeavyTape D) (t : ℕ) :
    HeavyRecords.State X (HeavySlot X) D.r :=
  HeavyProcess.slice D.base D.positive.le (by simp [HeavySlot]) D.heavyFlag D.point N ω t

def heavyKey (D : Data X N H) (ω : Tape D) (t : ℕ) (p : X) : Option (Label D) :=
  (HeavyRecords.key (D.heavyState ω.1 t) p).map Sum.inl

def tierKey (D : Data X N H) (ω : Tape D) (t : ℕ) (i : Fin H) (p : X) : Option (Label D) :=
  (TierLabeledKeys.key D.r (D.K i) (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 p).map
    (fun l => Sum.inr (Sum.inl ⟨i,l⟩))

def key (D : Data X N H) (is : List (Fin H)) (ω : Tape D) (t : ℕ) (p : X) : Label D :=
  ((D.heavyKey ω t p).or (FirstStructure.first is (fun i => D.tierKey ω t i p))).getD (Sum.inr (Sum.inr p))

def anchor (D : Data X N H) (ω : Tape D) (t : ℕ) : Label D → X
  | Sum.inl l => (D.heavyState ω.1 t).center l
  | Sum.inr (Sum.inl ⟨i,l⟩) => TierLabeledKeys.anchor D.base D.r (D.K i) (D.qualify i) D.center t l
  | Sum.inr (Sum.inr p) => p

def tierLaw (D : Data X N H) (i : Fin H) : Law (TierTape D i) :=
  (TierLifetimes.law (N:=N) (D.K i) (D.quota i)).prod
    (Law.pi (fun _ : Fin N => TierRadius.law (X:=X) (Real.log (1+(D.K i:ℝ)^2)) D.r))

def law (D : Data X N H) : Law (Tape D) :=
  (Law.pi (fun _ : Fin N => HeavyRadius.law (X:=X) D.r)).prod (Law.pi D.tierLaw)

theorem first_witness {I J : Type*} (is : List I) (f : I → Option J) (j : J)
    (hj : FirstStructure.first is f=some j) : ∃ i∈is, f i=some j := by
  induction is with
  | nil => simp [FirstStructure.first] at hj
  | cons i is ih =>
    cases he : f i with
    | none =>
      have ht : FirstStructure.first is f=some j := by simpa only [FirstStructure.first,he,Option.none_or] using hj
      obtain ⟨a,ha,hf⟩ := ih ht
      exact ⟨a,List.mem_cons_of_mem _ ha,hf⟩
    | some k =>
      have hkj : k=j := Option.some.inj (by simpa only [FirstStructure.first,he,Option.some_or] using hj)
      exact ⟨i,List.mem_cons_self ..,hkj ▸ he⟩

theorem heavy_covers (D : Data X N H) (ω : Tape D) (t : ℕ) (p : X) (l : Label D)
    (hl : D.heavyKey ω t p=some l) : dist p (D.anchor ω t l)≤20*D.r := by
  obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hl
  have hc := (HeavyRecords.key_some _ D.positive.le p a).mp ha
  change dist p ((D.heavyState ω.1 t).center a)≤_
  rw [dist_comm]
  exact hc.2.trans ((D.heavyState ω.1 t).radius_bounds a hc.1).2

theorem tier_covers (D : Data X N H) (ω : Tape D) (t : ℕ) (i : Fin H) (p : X) (l : Label D)
    (hl : D.tierKey ω t i p=some l) : dist p (D.anchor ω t l)≤2*D.r := by
  obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hl
  exact TierLabeledKeys.covers D.base D.r D.positive (D.K i) (D.two i) (D.quota i)
    (D.qualify i) D.center t (ω.2 i).1 (ω.2 i).2 p a ha

theorem covers (D : Data X N H) (is : List (Fin H)) (ω : Tape D) (t : ℕ) (p : X) :
    dist p (D.anchor ω t (D.key is ω t p))≤20*D.r := by
  cases hh : D.heavyKey ω t p with
  | some l =>
    simpa only [key,hh,Option.some_or,Option.getD_some] using heavy_covers D ω t p l hh
  | none =>
    cases ht : FirstStructure.first is (fun i => D.tierKey ω t i p) with
    | none => simp only [key,hh,Option.none_or,ht,Option.getD_none,anchor,dist_self]; exact mul_nonneg (by norm_num) D.positive.le
    | some l =>
      obtain ⟨i,hi,hk⟩ := first_witness is _ l ht
      have hc := tier_covers D ω t i p l hk
      simp only [key,hh,Option.none_or,ht,Option.getD_some]
      linarith [D.positive]

theorem diameter (D : Data X N H) (is : List (Fin H)) (ω : Tape D) (t : ℕ) (p q : X)
    (he : D.key is ω t p=D.key is ω t q) : dist p q≤40*D.r := by
  have hp := covers D is ω t p
  have hq := covers D is ω t q
  rw [←he] at hq
  have ht := dist_triangle p (D.anchor ω t (D.key is ω t p)) q
  rw [dist_comm (D.anchor ω t (D.key is ω t p)) q] at ht
  linarith

end Data
end UniformKServer.LevelMap

end


end

end OAI

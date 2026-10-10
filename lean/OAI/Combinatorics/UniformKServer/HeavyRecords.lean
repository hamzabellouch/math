import Mathlib

namespace OAI

                                   
section

/-! Fixed-slot implementation of disjoint heavy balls, including the literal
finite-metric intersection test for label reuse. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset
open scoped Classical
variable {X Λ : Type*} [MetricSpace X] [Fintype Λ]

structure State (X Λ : Type*) [MetricSpace X] (r : ℝ) where
  present : Finset Λ
  center : Λ → X
  radius : Λ → ℝ
  radius_bounds : ∀ l ∈ present, radius l ∈ Set.Icc (16*r) (20*r)
  separated : ∀ a ∈ present, ∀ b ∈ present, a ≠ b → 100*r < dist (center a) (center b)

variable {r : ℝ}

def covers (S : State X Λ r) (l : Λ) (p : X) : Prop :=
  l ∈ S.present ∧ dist (S.center l) p ≤ S.radius l

omit [Fintype Λ] in
theorem unique (S : State X Λ r) (hr : 0 ≤ r) (a b : Λ) (p : X)
    (ha : covers S a p) (hb : covers S b p) : a=b := by
  by_contra hn
  have hh := S.separated a ha.1 b hb.1 hn
  have ht := dist_triangle (S.center a) p (S.center b)
  rw [dist_comm p (S.center b)] at ht
  linarith [(S.radius_bounds a ha.1).2,(S.radius_bounds b hb.1).2,ha.2,hb.2]

def key (S : State X Λ r) (p : X) : Option Λ :=
  if h : ∃ l, covers S l p then some (Classical.choose h) else none

theorem key_some (S : State X Λ r) (hr : 0 ≤ r) (p : X) (l : Λ) :
    key S p=some l ↔ covers S l p := by
  unfold key
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · intro he; rw [←he]; exact Classical.choose_spec h
    · intro hc; exact unique S hr _ _ p (Classical.choose_spec h) hc
  · constructor
    · intro h; cases h
    · intro hc; exact (h ⟨l,hc⟩).elim

theorem key_none (S : State X Λ r) (p : X) : key S p=none ↔ ¬∃ l, covers S l p := by
  unfold key
  split_ifs <;> simp_all

def intersects (S : State X Λ r) (x : X) (R : ℝ) (l : Λ) : Prop :=
  ∃ p, covers S l p ∧ dist x p ≤ R

omit [Fintype Λ] in
theorem intersect_distance (S : State X Λ r) (x : X) (R : ℝ) (l : Λ)
    (hR : R ≤ 20*r) (h : intersects S x R l) : dist x (S.center l) ≤ 40*r := by
  obtain ⟨p,hp,hd⟩ := h
  have ht := dist_triangle x p (S.center l)
  rw [dist_comm p (S.center l)] at ht
  linarith [(S.radius_bounds l hp.1).2,hp.2]

omit [Fintype Λ] in
theorem intersect_unique (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ≤ 20*r) (a b : Λ) (ha : intersects S x R a) (hb : intersects S x R b) : a=b := by
  by_contra hn
  have hh := S.separated a (Classical.choose_spec ha).1.1 b (Classical.choose_spec hb).1.1 hn
  have ha' := intersect_distance S x R a hR ha
  have hb' := intersect_distance S x R b hR hb
  have ht := dist_triangle (S.center a) x (S.center b)
  rw [dist_comm (S.center a) x] at ht
  linarith

def reused (S : State X Λ r) (x : X) (R : ℝ) : Option Λ :=
  if h : ∃ l, intersects S x R l then some (Classical.choose h) else none

def chosen (S : State X Λ r) (x : X) (R : ℝ) (fresh : Λ) : Λ :=
  (reused S x R).getD fresh

theorem chosen_of_intersects (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ≤ 20*r) (fresh l : Λ) (hl : intersects S x R l) : chosen S x R fresh=l := by
  unfold chosen reused
  rw [dite_eq_left ⟨l,hl⟩]
  exact intersect_unique S hr x R hR _ l (Classical.choose_spec _) hl

theorem chosen_cases (S : State X Λ r) (x : X) (R : ℝ) (fresh : Λ) :
    intersects S x R (chosen S x R fresh) ∨
      (chosen S x R fresh=fresh ∧ ¬∃ l, intersects S x R l) := by
  unfold chosen reused
  split_ifs with h
  · exact Or.inl (Classical.choose_spec h)
  · exact Or.inr ⟨rfl,h⟩

def survivors (S : State X Λ r) (x : X) : Finset Λ :=
  S.present.filter (fun l => 100*r < dist x (S.center l))

theorem chosen_not_survivor (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ≤ 20*r) (fresh : Λ) (hf : fresh ∉ S.present) : chosen S x R fresh ∉ survivors S x := by
  intro hc
  obtain ⟨hp,hd⟩ := mem_filter.mp hc
  rcases chosen_cases S x R fresh with hi | ⟨he,_⟩
  · have := intersect_distance S x R _ hR hi
    linarith
  · exact hf (he ▸ hp)

def insert (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) : State X Λ r where
  present := Insert.insert (chosen S x R fresh) (survivors S x)
  center := Function.update S.center (chosen S x R fresh) x
  radius := Function.update S.radius (chosen S x R fresh) R
  radius_bounds := by
    intro l hl
    rcases mem_insert.mp hl with he | hs
    · subst l
      simpa only [Function.update_self] using hR
    · have hn : l ≠ chosen S x R fresh := fun he => chosen_not_survivor S hr x R hR.2 fresh hf (he ▸ hs)
      rw [Function.update_of_ne hn]
      exact S.radius_bounds l (mem_filter.mp hs).1
  separated := by
    intro a ha b hb hn
    rcases mem_insert.mp ha with he | ha
    · subst a
      rcases mem_insert.mp hb with he | hb
      · exact (hn he.symm).elim
      · have hbne : b ≠ chosen S x R fresh := Ne.symm hn
        rw [Function.update_self,Function.update_of_ne hbne]
        exact (mem_filter.mp hb).2
    · have hane : a ≠ chosen S x R fresh := fun he => chosen_not_survivor S hr x R hR.2 fresh hf (he ▸ ha)
      rw [Function.update_of_ne hane]
      rcases mem_insert.mp hb with he | hb
      · subst b
        rw [Function.update_self,dist_comm]
        exact (mem_filter.mp ha).2
      · have hbne : b ≠ chosen S x R fresh := fun he => chosen_not_survivor S hr x R hR.2 fresh hf (he ▸ hb)
        rw [Function.update_of_ne hbne]
        exact S.separated a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 hn

theorem new_covers (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) (p : X)
    (hp : dist x p ≤ R) : covers (insert S hr x R hR fresh hf) (chosen S x R fresh) p := by
  constructor
  · exact mem_insert_self _ _
  · simpa only [insert,Function.update_self] using hp

theorem covers_insert_iff (S : State X Λ r) (hr : 0 ≤ r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) (l : Λ) (p : X) :
    covers (insert S hr x R hR fresh hf) l p ↔
      (l=chosen S x R fresh ∧ dist x p ≤ R) ∨ (l ∈ survivors S x ∧ covers S l p) := by
  by_cases hl : l=chosen S x R fresh
  · subst l
    have hn := chosen_not_survivor S hr x R hR.2 fresh hf
    simp only [covers,insert,mem_insert_self,true_and,Function.update_self,hn,false_and,or_false]
  · simp only [covers,insert,mem_insert,hl,false_or,Function.update_of_ne hl,false_and,false_or]
    constructor
    · intro h; exact ⟨h.1,(mem_filter.mp h.1).1,h.2⟩
    · intro h; exact ⟨h.1,h.2.2⟩

omit [Fintype Λ] in
theorem center_injective (S : State X Λ r) (hr : 0 ≤ r) :
    Set.InjOn S.center S.present := by
  intro a ha b hb he
  by_contra hn
  have := S.separated a ha b hb hn
  rw [he,dist_self] at this
  linarith

omit [Fintype Λ] in
theorem card_present [Fintype X] (S : State X Λ r) (hr : 0 ≤ r) :
    S.present.card ≤ Fintype.card X := by
  have h := card_image_of_injOn (center_injective S hr)
  rw [←h]
  exact card_le_card (subset_univ _)

end UniformKServer.HeavyRecords

end


end

end OAI

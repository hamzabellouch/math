import Mathlib
import OAI.Combinatorics.KMedian.Hardness.PartitionAverage

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

structure ProjectionSystem (U V I A B : Type) where
  neighbor : V → I → U
  project : V → I → A → B

namespace ProjectionSystem
variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

def labels (S : Finset (U × A)) (u : U) : Finset A :=
  univ.filter (fun a => (u,a) ∈ S)

omit [Fintype U] in
@[simp] theorem mem_labels (S : Finset (U × A)) (u : U) (a : A) :
    a ∈ labels S u ↔ (u,a) ∈ S := by simp [labels]

theorem labels_sum (S : Finset (U × A)) : ∑ u, (labels S u).card = S.card := by
  simp only [labels, card_eq_sum_ones, sum_filter]
  rw [← Fintype.sum_prod_type (fun p : U × A => if p ∈ S then (1 : ℕ) else 0)]
  simp

def parts (S : Finset (U × A)) (v : V) (b : B) : Finset I :=
  univ.filter (fun i => ∃ a ∈ labels S (G.neighbor v i), G.project v i a = b)

omit [Fintype U] [Fintype V] [Fintype B] [DecidableEq V] [DecidableEq I] in
@[simp] theorem mem_parts (S : Finset (U × A)) (v : V) (b : B) (i : I) :
    i ∈ G.parts S v b ↔ ∃ a, (G.neighbor v i,a) ∈ S ∧ G.project v i a = b := by
  simp [parts]

def covered (S : Finset (U × A)) : Finset (V × (B → I)) :=
  univ.filter (fun p => ∃ i a, (G.neighbor p.1 i,a) ∈ S ∧ p.2 (G.project p.1 i a) = i)

omit [Fintype U] [DecidableEq V] in
@[simp] theorem mem_covered (S : Finset (U × A)) (v : V) (w : B → I) :
    (v,w) ∈ G.covered S ↔ w ∈ Partitions.hit (G.parts S v) := by
  simp only [covered, mem_filter, mem_univ, true_and, Partitions.mem_hit, mem_parts]
  constructor
  · rintro ⟨i,a,ha,hw⟩
    refine ⟨G.project v i a,a,?_,?_⟩
    · simpa only [hw] using ha
    · simp only [hw]
  · rintro ⟨b,a,ha,hb⟩
    exact ⟨w b,a,ha,by rw [hb]⟩

omit [Fintype U] in
theorem covered_card (S : Finset (U × A)) :
    (G.covered S).card = ∑ v, (Partitions.hit (G.parts S v)).card := by
  conv_lhs => rw [card_eq_sum_ones]
  rw [← sum_ite_mem_eq]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro v _
  simp only [G.mem_covered, sum_boole, filter_mem_eq_inter, univ_inter, Nat.cast_id]

omit [DecidableEq V] in
theorem perfect_cover (left : U → A) (right : V → B)
    (h : ∀ v i, G.project v i (left (G.neighbor v i)) = right v) :
    ∃ S : Finset (U × A), S.card ≤ Fintype.card U ∧ G.covered S = univ := by
  let S : Finset (U × A) := univ.image (fun u => (u,left u))
  refine ⟨S, (card_image_le.trans (by simp)), ?_⟩
  apply eq_univ_of_forall
  rintro ⟨v,w⟩
  simp only [covered, mem_filter, mem_univ, true_and]
  refine ⟨w (right v),left (G.neighbor v (w (right v))),?_,?_⟩
  · exact mem_image_of_mem _ (mem_univ _)
  · rw [h]

def LeftRegular (d : ℕ) : Prop :=
  ∀ u, (univ.filter (fun p : V × I => G.neighbor p.1 p.2 = u)).card = d

omit [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B] in
theorem regular_sum {d : ℕ} (hreg : G.LeftRegular d) (f : U → ℕ) :
    (∑ v, ∑ i, f (G.neighbor v i)) = d * ∑ u, f u := by
  rw [← Fintype.sum_prod_type (fun p : V × I => f (G.neighbor p.1 p.2))]
  have he (p : V × I) : f (G.neighbor p.1 p.2) =
      ∑ u, if G.neighbor p.1 p.2 = u then f u else 0 := by simp
  simp_rw [he]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro u _
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, hreg u, Nat.cast_id]

omit [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B] in
theorem regular_degrees {d : ℕ} (hreg : G.LeftRegular d) :
    d * Fintype.card U = Fintype.card I * Fintype.card V := by
  have hh := G.regular_sum hreg (fun _ => 1)
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Nat.cast_id] at hh
  simpa only [mul_comm] using hh.symm

omit [Fintype U] [Fintype V] [DecidableEq V] [DecidableEq I] in
theorem active_le (S : Finset (U × A)) (v : V) :
    (Partitions.active (G.parts S v)).card ≤ ∑ i, (labels S (G.neighbor v i)).card := by
  let T : Finset (I × A) := univ.filter (fun p => (G.neighbor v p.1,p.2) ∈ S)
  have he : Partitions.active (G.parts S v) = T.image (fun p => G.project v p.1 p.2) := by
    ext b
    simp only [Partitions.mem_active, Finset.Nonempty, G.mem_parts, T,
      mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i,a,ha,hb⟩
      exact ⟨(i,a),ha,hb⟩
    · rintro ⟨⟨i,a⟩,ha,hb⟩
      exact ⟨i,a,ha,hb⟩
  have hc : T.card = ∑ i, (labels S (G.neighbor v i)).card := by
    simp only [T, labels, card_eq_sum_ones, sum_filter]
    rw [Fintype.sum_prod_type]
  rw [he, ← hc]
  exact card_image_le

omit [DecidableEq V] [DecidableEq I] in
theorem active_budget {d : ℕ} (hreg : G.LeftRegular d)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U) :
    ∑ v, (Partitions.active (G.parts S v)).card ≤ Fintype.card I * Fintype.card V := by
  calc
    _ ≤ ∑ v, ∑ i, (labels S (G.neighbor v i)).card :=
      sum_le_sum (fun v _ => G.active_le S v)
    _ = d * S.card := by rw [G.regular_sum hreg (fun u => (labels S u).card), labels_sum]
    _ ≤ d * Fintype.card U := Nat.mul_le_mul_left d hS
    _ = _ := G.regular_degrees hreg

def bad (S : Finset (U × A)) : Finset V :=
  univ.filter (fun v => ∃ b, 1 < (G.parts S v b).card)

omit [Fintype U] [DecidableEq V] [DecidableEq I] in
theorem good_functional (S : Finset (U × A)) {v : V} (hv : v ∉ G.bad S) :
    ∀ b, (G.parts S v b).card ≤ 1 := by
  simpa only [bad,mem_filter,mem_univ,true_and,not_exists,not_lt] using hv

theorem coverage_bound {d : ℕ} (hreg : G.LeftRegular d)
    (hI : 1 < Fintype.card I) (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U) :
    ((G.covered S).card:ℝ) ≤ (Fintype.card I:ℝ)^Fintype.card B *
      ((Fintype.card V:ℝ)*(1-(1-1/(Fintype.card I:ℝ))^Fintype.card I)+(G.bad S).card) := by
  rw [G.covered_card, Nat.cast_sum]
  exact Partitions.total_hit_bound (G.parts S) (G.bad S) hI
    (fun _ hv => G.good_functional S hv) (G.active_budget hreg S hS)

end ProjectionSystem
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI

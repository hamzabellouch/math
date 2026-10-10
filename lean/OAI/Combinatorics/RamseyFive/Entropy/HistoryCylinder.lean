import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.Hits
import OAI.Combinatorics.RamseyFive.Entropy.SequentialLaw
import OAI.Combinatorics.RamseyFive.Entropy.FinitePiLaw
import OAI.Combinatorics.RamseyFive.Streams.PermutationCylinder

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {Ω Τ I H A B : Type*} [Fintype Ω] [Fintype Τ]
  [Fintype I] [Fintype H] [Fintype A] [Fintype B]

lemma eventMass_independent_product (p : Law Ω) (q : Law Τ)
    (E : Finset Ω) (F : Finset Τ) :
    eventMass (adaptiveLaw p (fun _ => q)) (E ×ˢ F) =
      eventMass p E * eventMass q F := by
  change (∑ z ∈ E ×ˢ F, p z.1 * q z.2) = (∑ x ∈ E, p x) * ∑ y ∈ F, q y
  rw [Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]

lemma conditionOn_independent_product (p : Law Ω) (q : Law Τ)
    (E : Finset Ω) (F : Finset Τ) (hE : 0 < eventMass p E)
    (hF : 0 < eventMass q F) :
    conditionOn (adaptiveLaw p (fun _ => q)) (E ×ˢ F)
      (by rw [eventMass_independent_product]; exact mul_pos hE hF) =
      adaptiveLaw (conditionOn p E hE) (fun _ => conditionOn q F hF) := by
  classical
  apply Law.ext
  funext z
  rw [conditionOn_apply, eventMass_independent_product]
  simp only [adaptiveLaw, conditionOn]
  by_cases he : z.1 ∈ E <;> by_cases hf : z.2 ∈ F <;>
    simp [he, hf, div_mul_div_comm]

def indexValueHistory (indices : Τ → I) (expose : I → Ω → H) (z : Ω × Τ) : I × H :=
  (indices z.2, expose (indices z.2) z.1)

omit [Fintype I] [Fintype H] in
lemma history_rectangle (indices : Τ → I) (expose : I → Ω → H) (i : I) (h : H) :
    Finset.univ.filter (fun z => indexValueHistory indices expose z = (i,h)) =
      (Finset.univ.filter (fun x => expose i x = h)) ×ˢ
        (Finset.univ.filter (fun r => indices r = i)) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
    indexValueHistory, Prod.mk.injEq]
  constructor
  · rintro ⟨hi, hh⟩
    exact ⟨hi ▸ hh, hi⟩
  · rintro ⟨hh, hi⟩
    exact ⟨hi, hi.symm ▸ hh⟩

omit [Fintype I] [Fintype H] in
theorem history_factorization (p : Law Ω) (q : Law Τ)
    (indices : Τ → I) (expose : I → Ω → H) (i : I) (h : H)
    (hi : 0 < eventMass q (Finset.univ.filter (fun r => indices r = i)))
    (hh : 0 < eventMass p (Finset.univ.filter (fun x => expose i x = h))) :
    conditionOn (adaptiveLaw p (fun _ => q))
      (Finset.univ.filter (fun z => indexValueHistory indices expose z = (i,h)))
      (by rw [history_rectangle, eventMass_independent_product]; exact mul_pos hh hi) =
      adaptiveLaw
        (conditionOn p (Finset.univ.filter (fun x => expose i x = h)) hh)
        (fun _ => conditionOn q (Finset.univ.filter (fun r => indices r = i)) hi) := by
  simpa only [history_rectangle] using conditionOn_independent_product p q
    (Finset.univ.filter (fun x => expose i x = h))
    (Finset.univ.filter (fun r => indices r = i)) hh hi

lemma map_independent_pair (p : Law Ω) (q : Law Τ) (f : Ω → A) (g : Τ → B) :
    map (adaptiveLaw p (fun _ => q)) (fun z => (f z.1, g z.2)) =
      adaptiveLaw (map p f) (fun _ => map q g) := by
  classical
  apply Law.ext
  funext z
  simp only [map, adaptiveLaw]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have hz : (f x, g y) = z ↔ f x = z.1 ∧ g y = z.2 := Prod.ext_iff
  simp only [hz]
  by_cases hf : f x = z.1 <;> by_cases hg : g y = z.2 <;> simp [hf, hg]

end

open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def uniformType (α : Type*) [Fintype α] [Nonempty α] : Law α :=
  uniformOn Finset.univ Finset.univ_nonempty

lemma uniformType_mass [Nonempty α] (E : Finset α) :
    eventMass (uniformType α) E = (E.card : ℝ) / Fintype.card α := by
  simp only [uniformType, uniformOn_mass, Finset.inter_univ, Finset.card_univ]

lemma uniformType_event_pos [Nonempty α] (E : Finset α) (hE : E.Nonempty) :
    0 < eventMass (uniformType α) E := by
  rw [uniformType_mass]
  exact div_pos (by exact_mod_cast Finset.card_pos.mpr hE)
    (by exact_mod_cast Fintype.card_pos)

lemma conditionOn_uniformType [Nonempty α] (E : Finset α) (hE : E.Nonempty) :
    conditionOn (uniformType α) E (uniformType_event_pos E hE) = uniformOn E hE := by
  apply Law.ext
  funext a
  rw [conditionOn_apply, uniformType_mass]
  simp only [uniformType, uniformOn, Finset.mem_univ, ite_true, Finset.card_univ]
  by_cases ha : a ∈ E
  · simp only [ha, ite_true]
    have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp [ha]

lemma map_uniformType [Nonempty α] (f : α → β) (b : β) :
    map (uniformType α) f b =
      (Fintype.card {a : α // f a = b} : ℝ) / Fintype.card α := by
  classical
  simp only [map, uniformType, uniformOn, Finset.mem_univ, ite_true, Finset.card_univ]
  rw [←Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
  rfl

lemma map_uniformType_subtype (E : Finset α) (hE : E.Nonempty) :
    letI : Nonempty E := hE.to_subtype
    map (uniformType E) Subtype.val = uniformOn E hE := by
  classical
  let : Nonempty E := hE.to_subtype
  apply Law.ext
  funext a
  rw [map_uniformType]
  simp only [Fintype.card_coe, uniformOn]
  by_cases ha : a ∈ E
  · simp only [ha, ite_true]
    have he : Fintype.card {x : E // (x : α) = a} = 1 := by
      let : Unique {x : E // (x : α) = a} :=
        { default := ⟨⟨a, ha⟩, rfl⟩
          uniq x := by apply Subtype.ext; exact Subtype.ext x.property }
      exact Fintype.card_unique
    rw [he]
    simp
  · simp only [ha, ite_false]
    have he : IsEmpty {x : E // (x : α) = a} :=
      ⟨fun x => ha (x.property ▸ x.val.property)⟩
    let := he
    simp
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.PermutationCylinder
open FiniteEntropy
open scoped Classical BigOperators
variable {α : Type*} [Fintype α]

noncomputable instance cylinderNonempty (S : Finset α) (e : Equiv.Perm α) :
    Nonempty (Cylinder S e) := ⟨⟨e, by intro x hx; rfl⟩⟩

noncomputable def drawLaw (S : Finset α) (e : Equiv.Perm α) (x : α) : Law α :=
  map (uniformType (Cylinder S e)) (fun p => p.val x)

lemma drawLaw_available (S : Finset α) (e : Equiv.Perm α) {x y : α}
    (hx : x ∉ S) (hy : y ∉ S.map e.toEmbedding) :
    drawLaw S e x y = 1 / (Fintype.card α - S.card : ℕ) := by
  rw [drawLaw, map_uniformType]
  exact next_probability S e hx hy

lemma drawLaw_exposed (S : Finset α) (e : Equiv.Perm α) {x y : α}
    (hx : x ∉ S) (hy : y ∈ S.map e.toEmbedding) : drawLaw S e x y = 0 := by
  rw [drawLaw, map_uniformType]
  have he : IsEmpty {p : Cylinder S e // p.val x = y} := by
    constructor
    intro p
    obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp hy
    change e z = y at hzy
    have hzx : p.val.val z = p.val.val x := (p.val.property z hz).trans (hzy.trans p.property.symm)
    exact hx (p.val.val.injective hzx ▸ hz)
  let := he
  simp

theorem drawLaw_exact (S : Finset α) (e : Equiv.Perm α) {x : α} (hx : x ∉ S) (y : α) :
    drawLaw S e x y = if y ∈ S.map e.toEmbedding then (0 : ℝ)
      else (1 : ℝ) / (Fintype.card α - S.card : ℕ) := by
  by_cases hy : y ∈ S.map e.toEmbedding
  · rw [ite_eq_left hy]; exact drawLaw_exposed S e hx hy
  · rw [ite_eq_right hy]; exact drawLaw_available S e hx hy

end SharpRamseyFive.PermutationCylinder

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]

lemma map_uniformOn (E : Finset α) (hE : E.Nonempty) (f : α → β) (b : β) :
    map (uniformOn E hE) f b =
      ((E.filter (fun a => f a = b)).card : ℝ)/E.card := by
  simp only [map, uniformOn]
  rw [←Finset.sum_filter]
  simp only [←Finset.sum_filter, Finset.filter_filter]
  have he : Finset.univ.filter (fun a => f a = b ∧ a ∈ E) = E.filter (fun a => f a = b) := by
    ext a; simp [and_comm]
  rw [he, Finset.sum_const, nsmul_eq_mul]
  rfl
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.PermutationCylinder
open FiniteEntropy
open scoped Classical BigOperators
variable {α : Type*} [Fintype α]

def rankPrefix (S : Finset α) (p : Equiv.Perm α) : S → α := fun x => p x

noncomputable def cylinderSet (S : Finset α) (e : Equiv.Perm α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter (fun p => rankPrefix S p = rankPrefix S e)

lemma mem_cylinderSet (S : Finset α) (e p : Equiv.Perm α) :
    p ∈ cylinderSet S e ↔ ∀ x ∈ S, p x = e x := by
  simp only [cylinderSet, Finset.mem_filter, Finset.mem_univ, true_and,
    funext_iff, rankPrefix, Subtype.forall]

lemma cylinderSet_nonempty (S : Finset α) (e : Equiv.Perm α) :
    (cylinderSet S e).Nonempty :=
  ⟨e, (mem_cylinderSet S e e).mpr (fun _ _ => rfl)⟩

noncomputable def cylinderSetEquiv (S : Finset α) (e : Equiv.Perm α) :
    cylinderSet S e ≃ Cylinder S e :=
  Equiv.subtypeEquivRight (mem_cylinderSet S e)

lemma card_cylinderSet (S : Finset α) (e : Equiv.Perm α) :
    (cylinderSet S e).card = Fintype.card (Cylinder S e) := by
  rw [←Fintype.card_coe]
  exact Fintype.card_congr (cylinderSetEquiv S e)

noncomputable def filterNextEquiv (S : Finset α) (e : Equiv.Perm α) (x y : α) :
    ↥((cylinderSet S e).filter (fun p => p x = y)) ≃
      {p : Cylinder S e // p.val x = y} where
  toFun p := ⟨⟨p.val, (mem_cylinderSet S e p.val).mp
    (Finset.mem_filter.mp p.property).1⟩, (Finset.mem_filter.mp p.property).2⟩
  invFun p := ⟨p.val.val, Finset.mem_filter.mpr
    ⟨(mem_cylinderSet S e p.val.val).mpr p.val.property, p.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem posterior_draw (S : Finset α) (e : Equiv.Perm α) {x y : α}
    (hx : x ∉ S) (hy : y ∉ S.map e.toEmbedding) :
    map (conditionOn (uniformType (Equiv.Perm α)) (cylinderSet S e)
      (uniformType_event_pos _ (cylinderSet_nonempty S e))) (fun p => p x) y =
      1 / (Fintype.card α - S.card : ℕ) := by
  rw [conditionOn_uniformType _ (cylinderSet_nonempty S e), map_uniformOn, card_cylinderSet]
  have hn := Fintype.card_congr (filterNextEquiv S e x y)
  rw [Fintype.card_coe] at hn
  rw [hn]
  exact next_probability S e hx hy

end SharpRamseyFive.PermutationCylinder

end OAI

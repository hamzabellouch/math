import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

universe uU uE uJ

/-!
# Counting events on disjoint sets of coordinates

The sample space is the actual finite function space `U → E`, with uniform
probability given by cardinality divided by the cardinality of that space.
A coordinate-swap bijection proves independence of two events from their
literal disjoint supports. Finite intersections then follow by induction.
No independence hypothesis or distinctness within an individual tuple is used.
-/

namespace MetricEntropyDuality.FiniteProductCounting

open scoped BigOperators

variable {U : Type uU} {E : Type uE} [Fintype U] [DecidableEq U] [Fintype E] [DecidableEq E]

/-- Agreement on the named coordinates determines event membership. -/
def DependsOn (S : Finset U) (A : Finset (U → E)) : Prop :=
  ∀ ω η : U → E, (∀ u ∈ S, ω u = η u) → (ω ∈ A ↔ η ∈ A)

/-- Uniform probability on the complete finite product sample space. -/
noncomputable def prob (A : Finset (U → E)) : ℝ :=
  (A.card : ℝ) / (Fintype.card (U → E) : ℝ)

/-- Swap the two assignments outside `S`, retaining them on `S`. -/
def coordinateSwap (S : Finset U) (z : (U → E) × (U → E)) :
    (U → E) × (U → E) :=
  (fun u => if u ∈ S then z.1 u else z.2 u,
   fun u => if u ∈ S then z.2 u else z.1 u)

omit [Fintype U] [Fintype E] [DecidableEq E] in
theorem coordinateSwap_involutive (S : Finset U) :
    Function.Involutive (coordinateSwap (E := E) S) := by
  intro z
  apply Prod.ext <;> funext u <;> by_cases hu : u ∈ S <;> simp [coordinateSwap, hu]

/-- The two-event counting identity is a bijection of actual assignments. -/
theorem card_inter_mul_card_sample (S T : Finset U) (A B : Finset (U → E))
    (hA : DependsOn S A) (hB : DependsOn T B) (hST : Disjoint S T) :
    (A ∩ B).card * Fintype.card (U → E) = A.card * B.card := by
  have hforward : ∀ z ∈ (A ∩ B).product (Finset.univ : Finset (U → E)),
      coordinateSwap S z ∈ A.product B := by
    rintro ⟨x, y⟩ hz
    have hxA := (Finset.mem_inter.mp (Finset.mem_product.mp hz).1).1
    have hxB := (Finset.mem_inter.mp (Finset.mem_product.mp hz).1).2
    apply Finset.mem_product.mpr
    constructor
    · apply (hA _ x ?_).mpr hxA
      intro u hu
      simp [coordinateSwap, hu]
    · apply (hB _ x ?_).mpr hxB
      intro u huT
      have huS : u ∉ S := fun huS => Finset.disjoint_left.mp hST huS huT
      simp [coordinateSwap, huS]
  have hreverse : ∀ z ∈ A.product B,
      coordinateSwap S z ∈ (A ∩ B).product (Finset.univ : Finset (U → E)) := by
    rintro ⟨x, y⟩ hz
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_inter.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
    · apply (hA _ x ?_).mpr hx
      intro u hu
      simp [coordinateSwap, hu]
    · apply (hB _ y ?_).mpr hy
      intro u huT
      have huS : u ∉ S := fun huS => Finset.disjoint_left.mp hST huS huT
      simp [coordinateSwap, huS]
  have hc := Finset.card_nbij' (coordinateSwap S) (coordinateSwap S)
    hforward hreverse
    (fun z _ => coordinateSwap_involutive S z)
    (fun z _ => coordinateSwap_involutive S z)
  simpa only [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ] using hc

omit [DecidableEq E] in
theorem prob_nonneg (A : Finset (U → E)) : 0 ≤ prob A :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

section NonemptyAlphabet

variable [Nonempty E]

omit [DecidableEq E] in
theorem sample_card_pos : (0 : ℝ) < Fintype.card (U → E) := by
  exact Nat.cast_pos.mpr (Fintype.card_pos (α := U → E))

omit [DecidableEq E] in
@[simp] theorem prob_univ : prob (Finset.univ : Finset (U → E)) = 1 := by
  simp only [prob, Finset.card_univ, div_self (ne_of_gt (sample_card_pos (U := U) (E := E)))]

/-- Uniform independence is derived from disjoint coordinate supports. -/
theorem prob_inter (S T : Finset U) (A B : Finset (U → E))
    (hA : DependsOn S A) (hB : DependsOn T B) (hST : Disjoint S T) :
    prob (A ∩ B) = prob A * prob B := by
  have hN : (Fintype.card (U → E) : ℝ) ≠ 0 := ne_of_gt sample_card_pos
  have hcard : ((A ∩ B).card : ℝ) * (Fintype.card (U → E) : ℝ) =
      (A.card : ℝ) * (B.card : ℝ) := by
    simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℝ))
      (card_inter_mul_card_sample S T A B hA hB hST)
  unfold prob
  apply (div_eq_iff hN).mpr
  rw [mul_assoc, div_mul_cancel₀ _ hN, div_mul_eq_mul_div]
  exact (eq_div_iff hN).mpr hcard

end NonemptyAlphabet

/-- All indexed events hold; the index set and events are kept literally. -/
def allEvents {J : Type uJ} [DecidableEq J] (s : Finset J)
    (A : J → Finset (U → E)) : Finset (U → E) :=
  Finset.univ.filter fun ω => ∀ j ∈ s, ω ∈ A j

@[simp] theorem mem_allEvents {J : Type uJ} [DecidableEq J]
    (s : Finset J) (A : J → Finset (U → E)) (ω : U → E) :
    ω ∈ allEvents s A ↔ ∀ j ∈ s, ω ∈ A j := by
  simp [allEvents]

@[simp] theorem allEvents_empty {J : Type uJ} [DecidableEq J]
    (A : J → Finset (U → E)) : allEvents ∅ A = Finset.univ := by
  ext ω
  simp

theorem allEvents_insert {J : Type uJ} [DecidableEq J]
    (j : J) (s : Finset J) (A : J → Finset (U → E)) :
    allEvents (insert j s) A = A j ∩ allEvents s A := by
  ext ω
  simp

theorem dependsOn_allEvents {J : Type uJ} [DecidableEq J]
    (s : Finset J) (S : J → Finset U) (A : J → Finset (U → E))
    (hdep : ∀ j ∈ s, DependsOn (S j) (A j)) :
    DependsOn (s.biUnion S) (allEvents s A) := by
  intro ω η hagree
  simp only [mem_allEvents]
  have hiff (j : J) (hj : j ∈ s) : ω ∈ A j ↔ η ∈ A j :=
    hdep j hj ω η (fun u hu => hagree u (Finset.mem_biUnion.mpr ⟨j, hj, hu⟩))
  constructor
  · intro h j hj
    exact (hiff j hj).mp (h j hj)
  · intro h j hj
    exact (hiff j hj).mpr (h j hj)

section FiniteIntersection

variable [Nonempty E]

/-- Every finite family of events on pairwise disjoint supports factors. -/
theorem prob_allEvents_eq_prod {J : Type uJ} [DecidableEq J]
    (s : Finset J) (S : J → Finset U) (A : J → Finset (U → E))
    (hdep : ∀ j ∈ s, DependsOn (S j) (A j))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) :
    prob (allEvents s A) = ∏ j ∈ s, prob (A j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hdepS : ∀ j ∈ s, DependsOn (S j) (A j) :=
        fun j hj => hdep j (Finset.mem_insert_of_mem hj)
      have hdisjS : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → Disjoint (S j) (S l) :=
        fun j hj l hl => hdisj j (Finset.mem_insert_of_mem hj)
          l (Finset.mem_insert_of_mem hl)
      have hdisjI : Disjoint (S i) (s.biUnion S) := by
        apply (Finset.disjoint_biUnion_right (S i) s S).mpr
        intro j hj
        exact hdisj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
          (fun hij => hi (hij.symm ▸ hj))
      rw [allEvents_insert, prob_inter (S i) (s.biUnion S) (A i) (allEvents s A)
        (hdep i (Finset.mem_insert_self _ _)) (dependsOn_allEvents s S A hdepS) hdisjI,
        ih hdepS hdisjS, Finset.prod_insert hi]

theorem prob_all_univ_eq_prod {w : ℕ} (S : Fin w → Finset U)
    (A : Fin w → Finset (U → E))
    (hdep : ∀ j, DependsOn (S j) (A j))
    (hdisj : Pairwise fun i j => Disjoint (S i) (S j)) :
    prob (allEvents Finset.univ A) = ∏ j, prob (A j) :=
  prob_allEvents_eq_prod Finset.univ S A (fun j _ => hdep j)
    (fun _ _ _ _ hij => hdisj hij)

/-- The repeated-event bound follows from the proved finite product identity. -/
theorem prob_all_univ_le_pow {w : ℕ} (S : Fin w → Finset U)
    (A : Fin w → Finset (U → E))
    (hdep : ∀ j, DependsOn (S j) (A j))
    (hdisj : Pairwise fun i j => Disjoint (S i) (S j))
    (b : ℝ) (hbound : ∀ j, prob (A j) ≤ b) :
    prob (allEvents Finset.univ A) ≤ b ^ w := by
  rw [prob_all_univ_eq_prod S A hdep hdisj]
  calc
    (∏ j, prob (A j)) ≤ ∏ _j : Fin w, b :=
      Finset.prod_le_prod₀ (fun index _ => prob_nonneg (A index))
        (fun index _ => hbound index)
    _ = b ^ w := by simp

end FiniteIntersection

end MetricEntropyDuality.FiniteProductCounting

end OAI

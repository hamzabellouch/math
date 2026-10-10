import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Probability.TailGraph
import OAI.Combinatorics.BalancedRyser.Probability.TailProductBounds
import OAI.Combinatorics.BalancedRyser.Probability.TailWeights

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
namespace TailGraph

variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]

omit [DecidableEq V] in
@[simp] theorem mem_slotVertices (slot : V → I) (i : I) (v : V) :
    v ∈ slotVertices slot i ↔ slot v = i := by
  simp [slotVertices]

omit [DecidableEq V] in
@[simp] theorem edgeWeight_mk (slot : V → I) (u v : V) :
    edgeWeight slot s(u, v) =
      2 / ((slotSize slot (slot u) : ℝ) * (slotSize slot (slot v) : ℝ)) := rfl

omit [DecidableEq V] in
theorem edgeWeight_nonneg (slot : V → I) (e : Sym2 V) :
    0 ≤ edgeWeight slot e := by
  induction e using Sym2.inductionOn with
  | _ u v => simp only [edgeWeight_mk]; positivity

omit [Fintype V] in
theorem edgeSlots_card_le_two (slot : V → I) (e : Sym2 V) :
    (edgeSlots slot e).card ≤ 2 := by
  apply Finset.card_image_le.trans
  rw [Sym2.card_toFinset]
  split_ifs <;> omega

omit [DecidableEq V] in
theorem edgeWeight_le_of_mem (slot : V → I) (L : ℕ) (hL : 0 < L)
    (hsize : ∀ i, L ≤ slotSize slot i) (u : V) (e : Sym2 V) (hu : u ∈ e) :
    edgeWeight slot e ≤ 2 / ((slotSize slot (slot u) : ℝ) * (L : ℝ)) := by
  rw [← Sym2.other_spec hu, edgeWeight_mk]
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have husize : (0 : ℝ) < slotSize slot (slot u) := by
    exact_mod_cast lt_of_lt_of_le hL (hsize (slot u))
  apply div_le_div_of_nonneg_left (by norm_num)
  · positivity
  · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hsize (slot (Sym2.Mem.other hu)))
      husize.le

omit [DecidableEq V] in
theorem incidence_weight_le (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I)
    (L : ℕ) (hL : 0 < L) (hsize : ∀ i, L ≤ slotSize slot i) (u : V) :
    ∑ e ∈ G.incidenceFinset u, edgeWeight slot e ≤
      (G.degree u : ℝ) * (2 / ((slotSize slot (slot u) : ℝ) * (L : ℝ))) := by
  classical
  calc
    _ ≤ ∑ _e ∈ G.incidenceFinset u,
        2 / ((slotSize slot (slot u) : ℝ) * (L : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      exact edgeWeight_le_of_mem slot L hL hsize u e
        (G.mem_incidenceFinset.mp he).2
    _ = _ := by simp

theorem slot_weight_le (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I)
    (L Δ : ℕ) (hL : 0 < L) (hsize : ∀ i, L ≤ slotSize slot i)
    (hdegree : ∀ u, G.degree u ≤ Δ) (i : I) :
    ∑ e ∈ slotEdges G slot i, edgeWeight slot e ≤ 2 * (Δ : ℝ) / (L : ℝ) := by
  classical
  have hLi : (0 : ℝ) < slotSize slot i := by
    exact_mod_cast lt_of_lt_of_le hL (hsize i)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hfilter : slotEdges G slot i = G.edgeFinset.filter
      (fun e => ∃ u ∈ slotVertices slot i, u ∈ e) := by
    ext e
    simp only [slotEdges, Finset.mem_filter, edgeSlots, Finset.mem_image,
      Sym2.mem_toFinset, mem_slotVertices]
    aesop
  rw [hfilter]
  calc
    _ ≤ ∑ u ∈ slotVertices slot i,
        ∑ e ∈ G.edgeFinset.filter (fun e => u ∈ e), edgeWeight slot e :=
      TailWeights.sum_filter_exists_le _ _ (fun u e => u ∈ e) _
        (fun e _ => edgeWeight_nonneg slot e)
    _ = ∑ u ∈ slotVertices slot i, ∑ e ∈ G.incidenceFinset u, edgeWeight slot e := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [G.incidenceFinset_eq_filter]
    _ ≤ ∑ _u ∈ slotVertices slot i,
        (Δ : ℝ) * (2 / ((slotSize slot i : ℝ) * (L : ℝ))) := by
      apply Finset.sum_le_sum
      intro u hu
      have hui : slot u = i := (mem_slotVertices slot i u).mp hu
      calc
        _ ≤ (G.degree u : ℝ) * (2 / ((slotSize slot (slot u) : ℝ) * (L : ℝ))) :=
          incidence_weight_le G slot L hL hsize u
        _ ≤ (Δ : ℝ) * (2 / ((slotSize slot i : ℝ) * (L : ℝ))) := by
          rw [hui]
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hdegree u
          · positivity
    _ = 2 * (Δ : ℝ) / (L : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      change (slotSize slot i : ℝ) * ((Δ : ℝ) *
        (2 / ((slotSize slot i : ℝ) * (L : ℝ)))) = _
      field_simp

theorem slot_weight_le_quarter (G : SimpleGraph V) [DecidableRel G.Adj] (slot : V → I)
    (L Δ : ℕ) (hL : 0 < L) (hsize : ∀ i, L ≤ slotSize slot i)
    (hdegree : ∀ u, G.degree u ≤ Δ) (hsparse : 8 * Δ ≤ L) (i : I) :
    ∑ e ∈ slotEdges G slot i, edgeWeight slot e ≤ 1 / 4 := by
  apply (slot_weight_le G slot L Δ hL hsize hdegree i).trans
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  apply (div_le_iff₀ hLr).2
  have hs : (8 : ℝ) * Δ ≤ L := by exact_mod_cast hsparse
  linarith

omit [DecidableEq V] in
theorem edgeWeight_le_half (slot : V → I) (hsize : ∀ i, 3 ≤ slotSize slot i)
    (e : Sym2 V) : edgeWeight slot e ≤ 1 / 2 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [edgeWeight_mk]
    have hu : (3 : ℝ) ≤ slotSize slot (slot u) := by exact_mod_cast hsize (slot u)
    have hv : (3 : ℝ) ≤ slotSize slot (slot v) := by exact_mod_cast hsize (slot v)
    have hp : (0 : ℝ) < (slotSize slot (slot u) : ℝ) * (slotSize slot (slot v) : ℝ) := by
      positivity
    apply (div_le_iff₀ hp).2
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (slotSize slot (slot u) : ℝ) - 3 by linarith)
      (show (0 : ℝ) ≤ (slotSize slot (slot v) : ℝ) - 3 by linarith)]

theorem touching_weight_le_quarter (G : SimpleGraph V) [DecidableRel G.Adj]
    (slot : V → I) (L Δ : ℕ) (hL : 0 < L)
    (hsize : ∀ i, L ≤ slotSize slot i) (hdegree : ∀ u, G.degree u ≤ Δ)
    (hsparse : 8 * Δ ≤ L) (J : Finset I) :
    ∑ e ∈ touchingEdges G slot J, edgeWeight slot e ≤ (J.card : ℝ) / 4 := by
  classical
  unfold touchingEdges
  simpa [div_eq_mul_inv] using
    TailWeights.touching_weight_le J G.edgeFinset
      (fun i e => i ∈ edgeSlots slot e) (edgeWeight slot) (1 / 4)
      (fun e _ => edgeWeight_nonneg slot e)
      (fun i _ => slot_weight_le_quarter G slot L Δ hL hsize hdegree hsparse i)

theorem dependency_weight_le_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (slot : V → I) (L Δ : ℕ) (hL : 0 < L)
    (hsize : ∀ i, L ≤ slotSize slot i) (hdegree : ∀ u, G.degree u ≤ Δ)
    (hsparse : 8 * Δ ≤ L) (e : Sym2 V) :
    ∑ f ∈ dependencyEdges G slot e, edgeWeight slot f ≤ 1 / 2 := by
  classical
  have h := touching_weight_le_quarter G slot L Δ hL hsize hdegree hsparse
    (edgeSlots slot e)
  have hc : ((edgeSlots slot e).card : ℝ) ≤ 2 := by
    exact_mod_cast edgeSlots_card_le_two slot e
  have hsub : ∑ f ∈ dependencyEdges G slot e, edgeWeight slot f ≤
      ∑ f ∈ touchingEdges G slot (edgeSlots slot e), edgeWeight slot f := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    intro f hf _
    exact edgeWeight_nonneg slot f
  linarith

theorem touching_inverse_product_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (slot : V → I) (L Δ : ℕ) (hL : 3 ≤ L)
    (hsize : ∀ i, L ≤ slotSize slot i) (hdegree : ∀ u, G.degree u ≤ Δ)
    (hsparse : 8 * Δ ≤ L) (J : Finset I) :
    ∏ e ∈ touchingEdges G slot J, (1 - edgeWeight slot e)⁻¹ ≤
      Real.exp ((J.card : ℝ) / 2) := by
  apply TailProduct.prod_inv_one_sub_le_exp_half
  · intro e he
    exact edgeWeight_nonneg slot e
  · intro e he
    exact edgeWeight_le_half slot (fun i => hL.trans (hsize i)) e
  · exact touching_weight_le_quarter G slot L Δ (by omega) hsize hdegree hsparse J

theorem mem_dependencyEdges_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (slot : V → I) (e f : Sym2 V) :
    f ∈ dependencyEdges G slot e ↔
      f ∈ G.edgeFinset ∧ f ≠ e ∧ ¬ Disjoint (edgeSlots slot e) (edgeSlots slot f) := by
  classical
  simp only [dependencyEdges, Finset.mem_erase, touchingEdges, Finset.mem_filter]
  rw [Finset.not_disjoint_iff]
  aesop

def liftEdges (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset (Sym2 V)) :
    Finset G.edgeSet := Finset.univ.filter (fun e => e.val ∈ s)

@[simp] theorem mem_liftEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset (Sym2 V)) (e : G.edgeSet) :
    e ∈ liftEdges G s ↔ e.val ∈ s := by simp [liftEdges]

theorem sum_liftEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset (Sym2 V)) (hs : s ⊆ G.edgeFinset) (w : Sym2 V → ℝ) :
    ∑ e ∈ liftEdges G s, w e.val = ∑ e ∈ s, w e := by
  classical
  apply Finset.sum_bij (fun e _ => e.val)
  · intro e he
    exact (mem_liftEdges G s e).mp he
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro e he
    refine ⟨⟨e, G.mem_edgeFinset.mp (hs he)⟩, ?_, rfl⟩
    exact (mem_liftEdges G s _).mpr he
  · intro e he
    rfl

theorem touchingEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (slot : V → I) (J : Finset I) : touchingEdges G slot J ⊆ G.edgeFinset :=
  Finset.filter_subset _ _

theorem dependencyEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (slot : V → I) (e : Sym2 V) : dependencyEdges G slot e ⊆ G.edgeFinset :=
  (Finset.erase_subset _ _).trans (touchingEdges_subset G slot (edgeSlots slot e))

end TailGraph
end Balanced

end OAI

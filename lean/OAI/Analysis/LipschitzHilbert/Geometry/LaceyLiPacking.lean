import OAI.Analysis.LipschitzHilbert.Estimates.PublishedInputs

namespace OAI

/-! Weighted distribution bounds for disjoint popularity witnesses,
derived directly from the cited finite-rectangle Lacey--Li input. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert

theorem laceyLi_weighted_tail (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (v : Plane → Plane) (K δ : ℝ≥0),
      LipschitzWith K v → (∀ x, ‖v x‖ = 1) → 0 < δ → δ < 1 →
      ∀ (n : ℕ) (R : Fin n → Rectangle), (∀ i, (R i).Admissible v K δ) →
      ∀ (E : Fin n → Set Plane) (w : Fin n → ℝ≥0∞) (α : ℝ≥0∞),
      (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i, E i ⊆ (R i).carrier) → (∀ i, α*w i ≤ volume (E i)) →
      ∀ (h : Plane → ℝ), MemLp h 2 volume →
      ∀ (a : Fin n → ℝ), (∀ i, ENNReal.ofReal (a i) ≤ (R i).average h) →
      ∀ t : ℝ≥0, 0 < t →
        (t : ℝ≥0∞)^2*α*(∑ i, if (t:ℝ) < a i then w i else 0) ≤
          (C : ℝ≥0∞)^2/(δ:ℝ≥0∞)*squareIntegral volume h := by
  classical
  obtain ⟨C,hC,hbound⟩ := hLL
  refine ⟨C,hC,?_⟩
  intro v K δ hv hu hδ hδ1 n R hR E w α hE hdisj hsub hsize h hh a ha t ht
  let F : Fin n → Set Plane := fun i => if (t:ℝ) < a i then E i else ∅
  let level : Set Plane := {x | (t:ℝ≥0∞) < rectangleMaximum R h x}
  have hFmeas : ∀ i, MeasurableSet (F i) := by
    intro i; dsimp [F]; split_ifs <;> simp_all
  have hFsub (i : Fin n) : F i ⊆ E i := by
    dsimp [F]; split_ifs <;> simp
  have hFd : Pairwise fun i j => Disjoint (F i) (F j) := by
    intro i j hij
    exact (hdisj hij).mono (hFsub i) (hFsub j)
  have hlevel (i : Fin n) : F i ⊆ level := by
    intro x hx
    by_cases hi : (t:ℝ) < a i
    · have hEi : x ∈ E i := hFsub i hx
      have hmx : (R i).average h ≤ rectangleMaximum R h x := by
        simpa only [rectangleMaximum, ite_eq_left (hsub i hEi)] using
          (Finset.le_sup (f := fun j => if x ∈ (R j).carrier then (R j).average h else 0)
            (Finset.mem_univ i))
      have ht' : (t:ℝ≥0∞) < ENNReal.ofReal (a i) := by
        have htR : (0:ℝ) < t := by exact_mod_cast ht
        simpa only [ENNReal.ofReal_coe_nnreal] using
          (ENNReal.ofReal_lt_ofReal_iff (htR.trans hi)).mpr hi
      exact ht'.trans_le ((ha i).trans hmx)
    · simp [F, hi] at hx
  have hpack := disjoint_witness_packing volume F (fun _ => level)
    (fun i => if (t:ℝ) < a i then w i else 0) α hFmeas hFd hlevel (by
      intro i; dsimp [F]; split_ifs with hi
      · exact hsize i
      · simp)
  have hp : α*(∑ i, if (t:ℝ) < a i then w i else 0) ≤ volume level :=
    hpack.trans (measure_mono (iUnion_subset (fun _ => Subset.rfl)))
  calc
    _ = (t:ℝ≥0∞)^2*(α*(∑ i, if (t:ℝ) < a i then w i else 0)) := by ring
    _ ≤ (t:ℝ≥0∞)^2*volume level := mul_le_mul' le_rfl hp
    _ ≤ _ := hbound v K δ hv hu hδ hδ1 n R hR h hh t ht

theorem laceyLi_weighted_tail_fintype (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (v : Plane → Plane) (K δ : ℝ≥0),
      LipschitzWith K v → (∀ x, ‖v x‖ = 1) → 0 < δ → δ < 1 →
      ∀ (ι : Type*) [Fintype ι] (R : ι → Rectangle), (∀ i, (R i).Admissible v K δ) →
      ∀ (E : ι → Set Plane) (w : ι → ℝ≥0∞) (α : ℝ≥0∞),
      (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i, E i ⊆ (R i).carrier) → (∀ i, α*w i ≤ volume (E i)) →
      ∀ (h : Plane → ℝ), MemLp h 2 volume →
      ∀ (a : ι → ℝ), (∀ i, ENNReal.ofReal (a i) ≤ (R i).average h) →
      ∀ t : ℝ≥0, 0 < t →
        (t : ℝ≥0∞)^2*α*(∑ i, if (t:ℝ) < a i then w i else 0) ≤
          (C : ℝ≥0∞)^2/(δ:ℝ≥0∞)*squareIntegral volume h := by
  classical
  obtain ⟨C,hC,hbound⟩ := laceyLi_weighted_tail hLL
  refine ⟨C,hC,?_⟩
  intro v K δ hv hu hδ hδ1 ι _ R hR E w α hE hdisj hsub hsize h hh a ha t ht
  let e := (Fintype.equivFin ι).symm
  have h := hbound v K δ hv hu hδ hδ1 (Fintype.card ι) (R ∘ e)
    (fun i => hR (e i)) (E ∘ e) (w ∘ e) α (fun i => hE (e i))
    (fun i j hij => hdisj (fun heq => hij (e.injective heq)))
    (fun i => hsub (e i)) (fun i => hsize (e i)) h hh (a ∘ e) (fun i => ha (e i)) t ht
  simpa only [Function.comp_apply, e.sum_comp (fun i => if (t:ℝ) < a i then w i else 0)] using h

end LipschitzHilbert

end

end OAI

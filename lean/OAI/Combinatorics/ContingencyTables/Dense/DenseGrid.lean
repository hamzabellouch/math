import OAI.Combinatorics.ContingencyTables.Dense.DenseRegularity
import OAI.Combinatorics.ContingencyTables.Dense.GridConductance

namespace OAI

/-!
# Conductance geometry for the actual dense penalty

The free table coordinates are reindexed by `Fin q`. The bin and cut-tube
density comparisons below follow from the actual margins and integer
widths. Thus the weighted cut theorem has no assumed penalty regularity
or bin comparison when used for the dense completion sampler.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {q : ℕ}

def realCorner {K : ℕ} (a : Grid (I := Fin q) K) : Fin q → ℝ :=
  fun j => (corner a j : ℝ)

def denseGridPenalty (R : Option I → ℕ) (P : Option J → ℕ) (d : ℕ)
    (e : I × J ≃ Fin q) (x : Fin q → ℝ) : ℝ :=
  DenseAffine.densePenalty R P d (fun p => x (e p))

theorem denseGridPenalty_continuous (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (e : I × J ≃ Fin q) : Continuous (denseGridPenalty R P d e) := by
  exact (DenseAffine.densePenalty_continuous R P d).comp
    (continuous_pi fun p => continuous_apply (e p))

theorem denseGridPenalty_convex (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (e : I × J ≃ Fin q) :
    ConvexOn ℝ Set.univ (denseGridPenalty R P d e) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  exact (DenseAffine.densePenalty_convex R P d Set.univ convex_univ).2
    (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem denseGridPenalty_change (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (x y : Fin q → ℝ) (r : ℝ) (hr : 0 ≤ r) (hxy : ∀ j, |x j - y j| ≤ r) :
    |(d : ℝ) ^ 4 * denseGridPenalty R P d e x -
      (d : ℝ) ^ 4 * denseGridPenalty R P d e y| ≤ r :=
  DenseAffine.densePenalty_scaled_change R P d hd hR hP hRmax hPmax hfree
    _ _ r hr (fun p => hxy (e p))

private theorem closedBin_distance {K : ℕ} (a : Grid (I := Fin q) K)
    (x : Fin q → ℝ) (hx : ClosedBin (corner a) x) :
    ∀ j, |x j - realCorner a j| ≤ 1 := by
  intro j
  change |x j - (corner a j : ℝ)| ≤ 1
  apply abs_le.mpr
  constructor <;> linarith [(hx j).1, (hx j).2]

private theorem tube_distances {K : ℕ} {Q : (Fin q → ℤ) → Prop}
    (edge : CutEdge K Q) (r : ℝ) (_hr : 0 ≤ r) (x : Fin q → ℝ)
    (hx : x ∈ edgeTube edge r) :
    (∀ j, |x j - realCorner edge.val.1 j| ≤ 1 + r) ∧
      (∀ j, |x j - realCorner edge.val.2.1 j| ≤ 1 + r) := by
  have hcoord (j : Fin q) := hx j (Set.mem_univ j)
  constructor
  · intro j
    have h := hcoord j
    dsimp [tubeLower, tubeUpper] at h
    change |x j - (corner edge.val.1 j : ℝ)| ≤ 1 + r
    by_cases hj : j = edge.val.2.2
    · subst j
      simp only [ite_true] at h
      apply abs_le.mpr
      constructor <;> linarith [h.1, h.2]
    · simp only [ite_eq_right hj] at h
      apply abs_le.mpr
      constructor <;> linarith [h.1, h.2]
  · intro j
    have h := hcoord j
    dsimp [tubeLower, tubeUpper] at h
    change |x j - (corner edge.val.2.1 j : ℝ)| ≤ 1 + r
    by_cases hj : j = edge.val.2.2
    · have hadj : (corner edge.val.2.1 j : ℝ) =
          (corner edge.val.1 j : ℝ) + 1 := by
        simpa only [hj, Int.cast_add, Int.cast_one] using
          congrArg (fun z : ℤ => (z : ℝ)) edge.property.1.1
      simp only [ite_eq_left hj] at h
      rw [hadj]
      apply abs_le.mpr
      constructor <;> linarith [h.1, h.2]
    · have heq : corner edge.val.2.1 j = corner edge.val.1 j :=
        congrArg Subtype.val (edge.property.1.2 j hj)
      simp only [ite_eq_right hj] at h
      rw [heq]
      apply abs_le.mpr
      constructor <;> linarith [h.1, h.2]

theorem denseGrid_bin_comparison (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    {K : ℕ} (a : Grid (I := Fin q) K) (x : Fin q → ℝ)
    (hx : ClosedBin (corner a) x) :
    DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner a) / 4 ≤
        DenseWeights.density ((d : ℝ) ^ 4) (denseGridPenalty R P d e) x ∧
      DenseWeights.density ((d : ℝ) ^ 4) (denseGridPenalty R P d e) x ≤
        2 * DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner a) :=
  DenseWeights.bin_density_comparison _ _ _ _
    (denseGridPenalty_change R P d hd hR hP hRmax hPmax hfree e x _ 1
      (by norm_num) (closedBin_distance a x hx))

theorem denseGrid_tube_comparison (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    {K : ℕ} {Q : (Fin q → ℤ) → Prop} (edge : CutEdge K Q) (r : ℝ)
    (hr : 0 ≤ r) (hr₁ : r ≤ 1) (x : Fin q → ℝ) (hx : x ∈ edgeTube edge r) :
    DenseWeights.density ((d : ℝ) ^ 4) (denseGridPenalty R P d e) x ≤
      4 * min
        (DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner edge.val.1))
        (DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner edge.val.2.1)) := by
  obtain ⟨hlo, hhi⟩ := tube_distances edge r hr x hx
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
  apply le_min
  · apply DenseWeights.tube_density_comparison
    exact (denseGridPenalty_change R P d hd hR hP hRmax hPmax hfree e x _ (1 + r)
      (by positivity) hlo).trans (by linarith)
  · apply DenseWeights.tube_density_comparison
    exact (denseGridPenalty_change R P d hd hR hP hRmax hPmax hfree e x _ (1 + r)
      (by positivity) hhi).trans (by linarith)

/-- Actual dyadic dense weights satisfy the interpolation cut bound,
conditionally only on the published finite-box integral inequality. -/
theorem denseGrid_weighted_cut (R : Option I → ℕ) (P : Option J → ℕ)
    (d : ℕ) (hd : 14 ≤ d) (hR : ∀ i, d ^ 12 ≤ R i) (hP : ∀ j, d ^ 12 ≤ P j)
    (hRmax : ∀ i, R (some i) ≤ R none) (hPmax : ∀ j, P (some j) ≤ P none)
    (hfree : Fintype.card (I × J) ≤ d) (e : I × J ≃ Fin q)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler q)
    {K : ℕ} (Q : (Fin q → ℤ) → Prop) (t : ℝ) (ht : 0 < t) (ht₁ : t < 1)
    (hr : t * K ≤ 1 / 4) (hsize : (q - 1 : ℕ) * (2 * (t * K)) ≤ (1 / 2 : ℝ))
    (hSmass : 0 < ∫ x in selectedBins K Q,
      DenseWeights.density ((d : ℝ) ^ 4) (denseGridPenalty R P d e) x)
    (hcut : 2 * (∫ x in selectedBins K Q,
      DenseWeights.density ((d : ℝ) ^ 4) (denseGridPenalty R P d e) x) ≤
      ∫ x in {x | Cube K x},
        DenseWeights.density ((d : ℝ) ^ 4) (denseGridPenalty R P d e) x) :
    (((2 : ℝ) ^ t - 1) / 16) *
        (∑ a : Selected K Q, DenseWeights.binWeight ((d : ℝ) ^ 4)
          (denseGridPenalty R P d e) (realCorner a.val)) ≤
      ∑ edge : CutEdge K Q, min
        (DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner edge.val.1))
        (DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner edge.val.2.1)) := by
  apply weighted_cut_of_interpolation hPL Q t ht ht₁ hr hsize
    (DenseWeights.density ((d : ℝ) ^ 4) (denseGridPenalty R P d e))
    (fun a => DenseWeights.binWeight ((d : ℝ) ^ 4) (denseGridPenalty R P d e) (realCorner a))
  · intro a
    exact (DenseWeights.binWeight_pos _ _ _).le
  · exact (DenseWeights.density_continuous _ _ (denseGridPenalty_continuous R P d e)).continuousOn
  · intro x _
    exact DenseWeights.density_pos _ _ _
  · intro x _ y _ s hs hs₁
    exact DenseWeights.density_logConcave _ (by positivity) _ Set.univ
      (denseGridPenalty_convex R P d e) x (Set.mem_univ _) y (Set.mem_univ _) s hs hs₁
  · intro a x hx
    exact (denseGrid_bin_comparison R P d hd hR hP hRmax hPmax hfree e a x
      (fun j => ⟨(hx j).1.le, (hx j).2.le⟩)).1
  · intro edge x hx
    exact denseGrid_tube_comparison R P d hd hR hP hRmax hPmax hfree e edge (t * K)
      (mul_nonneg ht.le (Nat.cast_nonneg _)) (by linarith) x hx.1
  · exact hSmass
  · exact hcut

end

end ContingencyTables.GridBoundary

end OAI

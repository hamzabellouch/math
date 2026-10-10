import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeodesicWords
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExtension

namespace OAI

/-! # Bounded-step words near a coarse chain

Sampling a coarse path gives finitely many jumps. Replacing each jump by a
short word in the unit ball gives a controlled word whose every prefix stays
near a sampled vertex. The minimizing-path hypothesis is the same concrete
metric hypothesis used by `GeodesicWords` and the stationary sublinearity bridge.
-/

namespace PolycyclicRecognition

open Metric Set

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G]

/-- A unit-step word has distance at most its length from the identity. -/
theorem dist_one_list_prod_le_length (w : List G)
    (hw : ∀ g ∈ w, g ∈ closedBall (1 : G) 1) :
    dist (1 : G) w.prod ≤ w.length := by
  induction w with
  | nil => simp
  | cons g w ih =>
    have hg : dist (1 : G) g ≤ 1 := by
      simpa only [mem_closedBall, dist_comm] using hw g (by simp)
    have ht := ih (fun x hx => hw x (by simp [hx]))
    calc
      dist (1 : G) (g :: w).prod ≤ dist (1 : G) g + dist g (g * w.prod) :=
        dist_triangle _ _ _
      _ = dist (1 : G) g + dist (1 : G) w.prod := by
        congr 1
        simpa only [mul_one] using dist_mul_left g (1 : G) w.prod
      _ ≤ 1 + (w.length : ℝ) := add_le_add hg ht
      _ = _ := by simp; ring

omit [MetricSpace G] [IsIsometricSMul G G] in
/-- Padding a finite word by identity letters preserves all its prefixes. -/
theorem wordPrefix_getD (w : List G) (j : ℕ) :
    wordPrefix (fun i => w.getD i 1) j = (w.take j).prod := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [wordPrefix_succ, ih]
    by_cases hj : j < w.length
    · rw [List.take_succ_eq_append_getElem hj, List.prod_append, List.prod_singleton]
      congr 1
      simp [List.getD, hj]
    · have hj' : w.length ≤ j := Nat.le_of_not_gt hj
      rw [List.take_of_length_le hj', List.take_of_length_le (by omega)]
      simp [List.getD, hj]

omit [IsIsometricSMul G G] in
/-- Identity padding keeps every increment inside the closed unit ball. -/
theorem getD_mem_closedBall_one (w : List G)
    (hw : ∀ g ∈ w, g ∈ closedBall (1 : G) 1) (i : ℕ) :
    w.getD i 1 ∈ closedBall (1 : G) 1 := by
  by_cases hi : i < w.length
  · simpa [List.getD, hi] using hw w[i] (List.getElem_mem hi)
  · simp [List.getD, hi]

/-- Replacing the jumps of a finite chain by unit-step words preserves the
endpoint, has controlled total length, and stays within one jump bound of
the sampled chain at every prefix. -/
theorem exists_word_near_chain
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (v : ℕ → G) (hv0 : v 0 = 1) {D : ℝ} (hD : 0 ≤ D) (n : ℕ)
    (hstep : ∀ i < n, dist (v i) (v (i + 1)) ≤ D) :
    ∃ w : List G, (∀ g ∈ w, g ∈ closedBall (1 : G) 1) ∧ w.prod = v n ∧
      (w.length : ℝ) ≤ (n : ℝ) * (D + 1) ∧
      ∀ j : ℕ, ∃ i ≤ n, dist (w.take j).prod (v i) ≤ D + 1 := by
  induction n with
  | zero =>
    refine ⟨[], by simp, by simpa using hv0.symm, by simp, ?_⟩
    intro j
    exact ⟨0, le_rfl, by simp [hv0]; linarith⟩
  | succ n ih =>
    obtain ⟨w, hw, hprod, hlen, hnear⟩ := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    obtain ⟨u, hu, huProd, huLen⟩ :=
      wordFactorization_of_minimizing_paths hpath ((v n)⁻¹ * v (n + 1))
    have hd : dist (1 : G) ((v n)⁻¹ * v (n + 1)) = dist (v n) (v (n + 1)) := by
      simpa only [mul_one, mul_inv_cancel_left] using
        (dist_mul_left (v n) (1 : G) ((v n)⁻¹ * v (n + 1))).symm
    have hlenU : (u.length : ℝ) ≤ D + 1 := by linarith [hstep n (Nat.lt_succ_self n)]
    refine ⟨w ++ u, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hw g hg
      · exact hu g hg
    · rw [List.prod_append, hprod, huProd, mul_inv_cancel_left]
    · simp only [List.length_append, Nat.cast_add, Nat.cast_succ]
      nlinarith
    · intro j
      by_cases hj : j ≤ w.length
      · rw [List.take_append_of_le_length hj]
        obtain ⟨i, hi, hdist⟩ := hnear j
        exact ⟨i, hi.trans (Nat.le_succ n), hdist⟩
      · have hj' : w.length ≤ j := by omega
        rw [List.take_append, List.take_of_length_le hj', List.prod_append, hprod]
        refine ⟨n, Nat.le_succ n, ?_⟩
        calc
          dist (v n * (u.take (j - w.length)).prod) (v n) =
              dist (1 : G) (u.take (j - w.length)).prod := by
            simpa only [mul_one, dist_comm] using
              dist_mul_left (v n) (u.take (j - w.length)).prod (1 : G)
          _ ≤ ((u.take (j - w.length)).length : ℝ) :=
            dist_one_list_prod_le_length _ (fun g hg => hu g (List.mem_of_mem_take hg))
          _ ≤ (u.length : ℝ) := by exact_mod_cast List.length_take_le' (j - w.length) u
          _ ≤ D + 1 := hlenU

end PolycyclicRecognition

end OAI

import OAI.Analysis.LipschitzHilbert.Trees.UnaryEnergy
import OAI.Analysis.LipschitzHilbert.Trees.BoundaryTelescoping

namespace OAI

/-!
# The unary-segment energy telescope

This is the finite cancellation behind §10, equation `src-28`. The actual
and propagated endpoint amounts agree, leaving only amplitude errors and
the small baseline-denominator corrections.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

private theorem log_add_baseline {V h : ℝ} (hV : 0 < V) (hh : 0 ≤ h) :
    Real.log (h + V) = Real.log V + Real.log (1 + h / V) := by
  rw [← Real.log_mul hV.ne' (show 1 + h / V ≠ 0 by positivity)]
  congr 1
  field_simp [hV.ne']
  ring

theorem unary_log_telescope (N : ℕ) (V W h beta : ℕ → ℝ)
    (hV : ∀ i ≤ N, 0 < V i) (hW : ∀ i ≤ N, 0 < W i)
    (hh : ∀ i < N, 0 ≤ h i) (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ V i / (h i + V (i + 1)))
    (hstar : ∀ i < N, W i ≤ h i + W (i + 1)) (hend : W N = V N) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤ Real.log (V 0 / W 0) +
      ∑ i ∈ Finset.range N,
        (Real.log (1 + h i / W (i + 1)) - Real.log (1 + h i / V (i + 1))) := by
  have hstep (i : ℕ) (hi : i < N) :
      Real.log (beta i) ≤
        ((Real.log (V i) - Real.log (W i)) -
          (Real.log (V (i + 1)) - Real.log (W (i + 1)))) +
        (Real.log (1 + h i / W (i + 1)) - Real.log (1 + h i / V (i + 1))) := by
    have hVnext := hV (i + 1) (by omega)
    have hWi := hW i hi.le
    have hWnext := hW (i + 1) (by omega)
    have hdenom : 0 < h i + V (i + 1) := add_pos_of_nonneg_of_pos (hh i hi) hVnext
    have hp := Real.log_le_log (mul_pos (hbeta i hi) hdenom)
      ((le_div_iff₀ hdenom).mp (hprediction i hi))
    rw [Real.log_mul (hbeta i hi).ne' hdenom.ne', log_add_baseline hVnext (hh i hi)] at hp
    have hs := Real.log_le_log hWi (hstar i hi)
    rw [log_add_baseline hWnext (hh i hi)] at hs
    linarith
  have htel : (∑ i ∈ Finset.range N,
      ((Real.log (V i) - Real.log (W i)) -
        (Real.log (V (i + 1)) - Real.log (W (i + 1))))) =
      Real.log (V 0 / W 0) := by
    have h := sum_range_shift_difference (fun i => Real.log (V i) - Real.log (W i)) N 1
    simpa only [Finset.sum_range_one, zero_add, hend, sub_self, sub_zero,
      Real.log_div (hV 0 (Nat.zero_le _)).ne' (hW 0 (Nat.zero_le _)).ne'] using h
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        (((Real.log (V i) - Real.log (W i)) -
          (Real.log (V (i + 1)) - Real.log (W (i + 1)))) +
          (Real.log (1 + h i / W (i + 1)) - Real.log (1 + h i / V (i + 1)))) :=
      Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)
    _ = _ := by rw [Finset.sum_add_distrib, htel]

/-- The telescope, with each surviving correction controlled by an
actual logarithmic-energy error and the relative baseline drop. -/
theorem unary_log_telescope_errors (N : ℕ) (V W n h beta error : ℕ → ℝ)
    (hn : ∀ i ≤ N, 0 < n i)
    (hV : ∀ i ≤ N, n i ≤ V i) (hW : ∀ i ≤ N, n i ≤ W i)
    (hh : ∀ i < N, 0 ≤ h i) (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ V i / (h i + V (i + 1)))
    (hstar : ∀ i < N, W i ≤ h i + W (i + 1)) (hend : W N = V N)
    (herror : ∀ i ≤ N, |Real.log (V i) - Real.log (W i)| ≤ error i) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤ error 0 +
      ∑ i ∈ Finset.range N, (h i / n (i + 1)) * error (i + 1) := by
  have hVp (i : ℕ) (hi : i ≤ N) := (hn i hi).trans_le (hV i hi)
  have hWp (i : ℕ) (hi : i ≤ N) := (hn i hi).trans_le (hW i hi)
  apply (unary_log_telescope N V W h beta hVp hWp hh hbeta hprediction hstar hend).trans
  apply add_le_add
  · rw [Real.log_div (hVp 0 (Nat.zero_le _)).ne' (hWp 0 (Nat.zero_le _)).ne']
    exact (le_abs_self _).trans (herror 0 (Nat.zero_le _))
  · apply Finset.sum_le_sum
    intro i hi
    have hin : i < N := Finset.mem_range.mp hi
    have hiN : i + 1 ≤ N := by omega
    have hc := log_correction_lipschitz (hh i hin) (hn (i + 1) hiN)
      (hW (i + 1) hiN) (hV (i + 1) hiN)
    have he : |Real.log (W (i + 1)) - Real.log (V (i + 1))| ≤ error (i + 1) := by
      simpa only [abs_sub_comm] using herror (i + 1) hiN
    exact (le_abs_self _).trans (hc.trans (mul_le_mul_of_nonneg_left he
      (div_nonneg (hh i hin) (hn (i + 1) hiN).le)))

section Vertex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Applying the scalar telescope to the actual vertex amounts gives
the finite form of `src-28` before the segment mass comparison. -/
theorem unary_vertex_telescope (N : ℕ) (n : ℕ → ℝ) (A Astar : ℕ → E)
    (beta : ℕ → ℝ) {a p D : ℝ} (hp : 1 ≤ p) (hap : a ≤ p)
    (hn : ∀ i ≤ N, 0 < n i) (hmass : ∀ i < N, n (i + 1) ≤ n i)
    (hcontraction : ∀ i < N, ‖Astar i‖ ≤ ‖Astar (i + 1)‖)
    (hend : Astar N = A N) (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ vertexAmount (n i) (A i) a p /
      (n i - n (i + 1) + vertexAmount (n (i + 1)) (A (i + 1)) a p))
    (herror : ∀ i ≤ N, ‖A i - Astar i‖ ≤ D) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤
      p * n 0 ^ ((a - 1) / p - 1) * D +
        ∑ i ∈ Finset.range N, ((n i - n (i + 1)) / n (i + 1)) *
          (p * n (i + 1) ^ ((a - 1) / p - 1) * D) := by
  apply unary_log_telescope_errors N
    (fun i => vertexAmount (n i) (A i) a p)
    (fun i => vertexAmount (n i) (Astar i) a p) n
    (fun i => n i - n (i + 1)) beta
    (fun i => p * n i ^ ((a - 1) / p - 1) * D) hn
  · exact fun i hi => mass_le_vertexAmount (hn i hi).le (A i)
  · exact fun i hi => mass_le_vertexAmount (hn i hi).le (Astar i)
  · exact fun i hi => sub_nonneg.mpr (hmass i hi)
  · exact hbeta
  · exact hprediction
  · intro i hi
    exact vertexAmount_subsolution (hn (i + 1) (by omega)) (hmass i hi) hap
      (by linarith) (Astar i) (Astar (i + 1)) (hcontraction i hi)
  · simp only [hend]
  · intro i hi
    exact (log_vertexAmount_lipschitz (hn i hi) hp (A i) (Astar i)).trans
      (mul_le_mul_of_nonneg_left (herror i hi)
        (mul_nonneg (by linarith) (Real.rpow_nonneg (hn i hi).le _)))

/-- A lower mass bound makes all the energy Lipschitz constants uniform.
Only the sum of relative drops remains; no factor counts unary indices. -/
theorem unary_vertex_telescope_uniform (N : ℕ) (n : ℕ → ℝ) (A Astar : ℕ → E)
    (beta : ℕ → ℝ) {a p D m : ℝ} (hp : 1 ≤ p) (hap : a ≤ p)
    (hm : 0 < m) (hD : 0 ≤ D) (hn : ∀ i ≤ N, m ≤ n i)
    (hmass : ∀ i < N, n (i + 1) ≤ n i)
    (hcontraction : ∀ i < N, ‖Astar i‖ ≤ ‖Astar (i + 1)‖)
    (hend : Astar N = A N) (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ vertexAmount (n i) (A i) a p /
      (n i - n (i + 1) + vertexAmount (n (i + 1)) (A (i + 1)) a p))
    (herror : ∀ i ≤ N, ‖A i - Astar i‖ ≤ D) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤
      (p * m ^ ((a - 1) / p - 1) * D) *
        (1 + ∑ i ∈ Finset.range N, (n i - n (i + 1)) / n (i + 1)) := by
  have hnp (i : ℕ) (hi : i ≤ N) : 0 < n i := hm.trans_le (hn i hi)
  have hexponent : (a - 1) / p - 1 ≤ 0 := by
    have hp0 : 0 < p := by linarith
    have hdiv : (a - 1) / p ≤ 1 := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  have hweight (i : ℕ) (hi : i ≤ N) :
      p * n i ^ ((a - 1) / p - 1) * D ≤ p * m ^ ((a - 1) / p - 1) * D := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hm (hn i hi) hexponent) (by linarith)) hD
  have h := unary_vertex_telescope N n A Astar beta hp hap hnp hmass
    hcontraction hend hbeta hprediction herror
  apply h.trans
  calc
    _ ≤ (p * m ^ ((a - 1) / p - 1) * D) +
        ∑ i ∈ Finset.range N, ((n i - n (i + 1)) / n (i + 1)) *
          (p * m ^ ((a - 1) / p - 1) * D) := by
      apply add_le_add (hweight 0 (Nat.zero_le _))
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      exact mul_le_mul_of_nonneg_left (hweight (i + 1) (by omega))
        (div_nonneg (sub_nonneg.mpr (hmass i hiN)) (hnp (i + 1) (by omega)).le)
    _ = _ := by rw [← Finset.sum_mul]; ring

end Vertex

/-- The mass drop over a segment telescopes even if the segment contains
arbitrarily many very small unary drops. -/
theorem segment_relative_drop_sum_le (N : ℕ) (n : ℕ → ℝ) {m : ℝ} (hm : 0 < m)
    (hn : ∀ i ≤ N, m ≤ n i) (hmass : ∀ i < N, n (i + 1) ≤ n i) :
    (∑ i ∈ Finset.range N, (n i - n (i + 1)) / n (i + 1)) ≤ (n 0 - n N) / m := by
  calc
    _ ≤ ∑ i ∈ Finset.range N, (n i - n (i + 1)) / m := by
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr (hmass i hiN)) hm (hn (i + 1) (by omega))
    _ = (∑ i ∈ Finset.range N, (n i - n (i + 1))) / m := (Finset.sum_div ..).symm
    _ = _ := by
      have h := sum_range_shift_difference n N 1
      simp only [Finset.sum_range_one, zero_add] at h
      rw [h]

theorem half_mass_rpow_le {x e : ℝ} (hx : 0 < x) (he : -1 ≤ e) :
    (x / 2) ^ e ≤ 2 * x ^ e := by
  have htwo : (2 : ℝ) ^ (-e) ≤ 2 := by
    calc
      (2 : ℝ) ^ (-e) ≤ 2 ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one _
  calc
    (x / 2) ^ e = x ^ e * (2 : ℝ) ^ (-e) := by
      rw [Real.div_rpow hx.le (by norm_num), div_eq_mul_inv, Real.rpow_neg (by norm_num)]
    _ ≤ x ^ e * 2 := mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hx.le _)
    _ = 2 * x ^ e := mul_comm _ _

/-- The final `src-28` estimate, with an explicit absolute constant, on
a segment whose total mass drop is at most two. -/
theorem unary_vertex_telescope_short_segment {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (n : ℕ → ℝ) (A Astar : ℕ → E) (beta : ℕ → ℝ)
    {a p D : ℝ} (hp : 1 ≤ p) (ha : 1 ≤ a) (hap : a ≤ p) (hD : 0 ≤ D)
    (hstart : 4 ≤ n 0) (hn : ∀ i ≤ N, n 0 - 2 ≤ n i)
    (hmass : ∀ i < N, n (i + 1) ≤ n i)
    (hcontraction : ∀ i < N, ‖Astar i‖ ≤ ‖Astar (i + 1)‖)
    (hend : Astar N = A N) (hbeta : ∀ i < N, 0 < beta i)
    (hprediction : ∀ i < N, beta i ≤ vertexAmount (n i) (A i) a p /
      (n i - n (i + 1) + vertexAmount (n (i + 1)) (A (i + 1)) a p))
    (herror : ∀ i ≤ N, ‖A i - Astar i‖ ≤ D) :
    (∑ i ∈ Finset.range N, Real.log (beta i)) ≤
      4 * p * n 0 ^ ((a - 1) / p - 1) * D := by
  have hp0 : 0 < p := by linarith
  have hn0 : 0 < n 0 := by linarith
  have hm : 0 < n 0 / 2 := by positivity
  have hnm (i : ℕ) (hi : i ≤ N) : n 0 / 2 ≤ n i := by
    linarith [hn i hi]
  have hrel := segment_relative_drop_sum_le N n hm hnm hmass
  have hrel1 : (∑ i ∈ Finset.range N, (n i - n (i + 1)) / n (i + 1)) ≤ 1 := by
    apply hrel.trans
    exact (div_le_one hm).mpr (by linarith [hn N le_rfl])
  have he : -1 ≤ (a - 1) / p - 1 := by
    have h := div_nonneg (sub_nonneg.mpr ha) hp0.le
    linarith
  have hhalf := half_mass_rpow_le hn0 he
  have hweight := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hhalf hp0.le) hD
  have hC : p * (n 0 / 2) ^ ((a - 1) / p - 1) * D ≤
      2 * (p * n 0 ^ ((a - 1) / p - 1) * D) := by nlinarith
  have hC0 : 0 ≤ p * (n 0 / 2) ^ ((a - 1) / p - 1) * D := by positivity
  calc
    _ ≤ (p * (n 0 / 2) ^ ((a - 1) / p - 1) * D) *
        (1 + ∑ i ∈ Finset.range N, (n i - n (i + 1)) / n (i + 1)) :=
      unary_vertex_telescope_uniform N n A Astar beta hp hap hm hD hnm hmass
        hcontraction hend hbeta hprediction herror
    _ ≤ (p * (n 0 / 2) ^ ((a - 1) / p - 1) * D) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    _ ≤ _ := by nlinarith

end LipschitzHilbert

end

end OAI

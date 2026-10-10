import OAI.Algebra.DepthFive.PathMassLowerBound
import OAI.Algebra.DepthFive.OccupationParameterBounds

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

open BidegreeAverages LowerParameters

/-- A Boolean layer choice includes all square-matrix coordinates in that layer. -/
theorem card_bool_layer_variables {n : ℕ} (side : Fin n → Bool) (ε : Bool) :
    Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = ε} =
      (Finset.univ.filter (fun t : Fin n => side t = ε)).card * n ^ 2 := by
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    card_layer_variables (Finset.univ.filter (fun t : Fin n => side t = ε))

/-- Uniform per-path first-moment estimate at the canonical lower-bound
parameters. Its only partition hypotheses are the two selected layer counts. -/
theorem immPath_source_mass_lower_parameters {n : ℕ} (hn : 16 ≤ n)
    (side : Fin n → Bool)
    (hk : (Finset.univ.filter (fun t : Fin n => side t = true)).card = k n)
    (hm : (Finset.univ.filter (fun t : Fin n => side t = false)).card = m n)
    [Fintype (Index (fun x : Fin n × Fin n × Fin n => side x.1) (a n) (b n))]
    (p : List (Fin n × Fin n × Fin n))
    (hp : p ∈ immPaths n (by omega)) :
    Real.exp (-64 / Real.sqrt (n : ℝ)) *
      (((a n : ℝ) / v n) ^ k n * (1 + (b n : ℝ) / u n) ^ m n) ≤
      (∑ d : Index (fun x : Fin n × Fin n × Fin n => side x.1) (a n) (b n),
        ((p.map (occupationAmplitude (fun x => side x.1) d.val)).prod) ^ 2) /
        (Fintype.card (Index (fun x : Fin n × Fin n × Fin n => side x.1)
          (a n) (b n)) : ℝ) := by
  have hn4 : 4 ≤ n := by omega
  have hv : Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = true} = v n := by
    rw [card_bool_layer_variables, hk]
    rfl
  have hu : Fintype.card {x : Fin n × Fin n × Fin n // side x.1 = false} = u n := by
    rw [card_bool_layer_variables, hm]
    rfl
  let : Nonempty {x : Fin n × Fin n × Fin n // side x.1 = true} :=
    Fintype.card_pos_iff.mp (by rw [hv]; exact v_pos hn4)
  let : Nonempty {x : Fin n × Fin n × Fin n // side x.1 = false} :=
    Fintype.card_pos_iff.mp (by rw [hu]; exact u_pos hn4)
  have hs : 2 * (Finset.univ.filter (fun t : Fin n => side t = true)).card ≤ a n := by
    rw [hk]
    have := four_mul_n_le_a hn
    have := k_le_n n
    omega
  have hz : 2 * (Finset.univ.filter (fun t : Fin n => side t = false)).card ≤ b n := by
    rw [hm]
    have := four_mul_n_le_b hn
    have := m_le_n n
    omega
  have hpath := immPath_source_mass_lower n (by omega) side (a n) (b n) p hp
    (a_pos hn4) (b_pos hn4) hs hz
  simp only [hk, hm, hv, hu] at hpath
  have hkn : (k n : ℝ) ≤ 2 * (n : ℝ) := by
    have h : (k n : ℝ) ≤ n := by exact_mod_cast k_le_n n
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hmn : (m n : ℝ) ≤ 2 * (n : ℝ) := by
    have h : (m n : ℝ) ≤ n := by exact_mod_cast m_le_n n
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hloss := occupation_two_orders_loss_le hn
    (Nat.cast_nonneg (α := ℝ) (k n)) hkn (Nat.cast_nonneg (α := ℝ) (m n)) hmn
  have hexp : Real.exp (-64 / Real.sqrt (n : ℝ)) ≤
      Real.exp ((-(k n : ℝ) ^ 2 / a n - (k n : ℝ) ^ 2 / (2 * (v n : ℝ))) +
        (-(m n : ℝ) ^ 2 / b n - (m n : ℝ) ^ 2 / (2 * (u n : ℝ)))) := by
    apply Real.exp_le_exp.mpr
    simp only [neg_div] at hloss ⊢
    linarith
  exact (mul_le_mul_of_nonneg_right hexp (by positivity)).trans hpath

/-- Unnormalized actual source sum. This form is directly summable over paths
in the first-trace identity, and requires no additional source-nonemptiness premise. -/
theorem immPath_source_sum_lower_parameters {n : ℕ} (hn : 16 ≤ n)
    (side : Fin n → Bool)
    (hk : (Finset.univ.filter (fun t : Fin n => side t = true)).card = k n)
    (hm : (Finset.univ.filter (fun t : Fin n => side t = false)).card = m n)
    [Fintype (Index (fun x : Fin n × Fin n × Fin n => side x.1) (a n) (b n))]
    (p : List (Fin n × Fin n × Fin n))
    (hp : p ∈ immPaths n (by omega)) :
    (Fintype.card (Index (fun x : Fin n × Fin n × Fin n => side x.1)
      (a n) (b n)) : ℝ) * Real.exp (-64 / Real.sqrt (n : ℝ)) *
      (((a n : ℝ) / v n) ^ k n * (1 + (b n : ℝ) / u n) ^ m n) ≤
      ∑ d : Index (fun x : Fin n × Fin n × Fin n => side x.1) (a n) (b n),
        ((p.map (occupationAmplitude (fun x => side x.1) d.val)).prod) ^ 2 := by
  have h := immPath_source_mass_lower_parameters hn side hk hm p hp
  by_cases hzero : Fintype.card (Index (fun x : Fin n × Fin n × Fin n => side x.1)
      (a n) (b n)) = 0
  · rw [hzero, Nat.cast_zero, zero_mul, zero_mul]
    exact Finset.sum_nonneg fun d _ => sq_nonneg _
  · have hpos : (0 : ℝ) < Fintype.card
        (Index (fun x : Fin n × Fin n × Fin n => side x.1) (a n) (b n)) := by
      exact_mod_cast Nat.pos_of_ne_zero hzero
    simpa only [mul_assoc, mul_left_comm, mul_comm] using (le_div_iff₀ hpos).mp h

end Problem335

end

end OAI

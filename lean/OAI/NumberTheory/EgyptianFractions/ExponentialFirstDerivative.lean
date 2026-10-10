import OAI.NumberTheory.EgyptianFractions.FirstDerivativeSum
import OAI.NumberTheory.EgyptianFractions.ReciprocalPhaseVariation

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337
open ReciprocalPhase

/-- A discrete first-derivative estimate, with an explicit absolute constant. -/
theorem exponential_first_derivative_bound (f d : ℕ → ℝ) (n : ℕ) (β : ℝ)
    (hβ : 0 < β) (hstep : ∀ j ≤ n, f (j + 1) = f j + d j)
    (hbounds : ∀ j ≤ n, β ≤ d j ∧ d j ≤ 1 - β)
    (hmono : (∀ j < n, d j ≤ d (j + 1)) ∨ (∀ j < n, d (j + 1) ≤ d j)) :
    ‖∑ j ∈ Finset.range (n + 1), unitPhase (Real.pi * f j)‖ ≤ 1 / β := by
  have hd (j : ℕ) (hj : j ≤ n) : d j ∈ Set.Ioo 0 1 := by
    obtain ⟨hl, hu⟩ := hbounds j hj
    constructor <;> linarith
  have hb (j : ℕ) (hj : j ≤ n) :
      ‖inversePhase (Real.pi * d j)‖ ≤ 1 / (4 * β) :=
    inversePhase_norm_le hβ (hbounds j hj).1 (hbounds j hj).2
  have h := first_derivative_sum_bound
    (fun j => unitPhase (Real.pi * f j))
    (fun j => inversePhase (Real.pi * d j)) n (1 / (4 * β))
    (fun j _ => le_of_eq (norm_unitPhase _)) hb
    (by
      intro j hj
      rw [inversePhase_scaled_re (hd j hj).1 (hd j hj).2,
        inversePhase_scaled_re (hd 0 (Nat.zero_le n)).1 (hd 0 (Nat.zero_le n)).2])
    (by
      rcases hmono with hmono | hanti
      · left
        intro j hj
        exact inversePhase_scaled_im_strictMonoOn.monotoneOn
          (hd j (by omega)) (hd (j + 1) (by omega)) (hmono j hj)
      · right
        intro j hj
        exact inversePhase_scaled_im_strictMonoOn.monotoneOn
          (hd (j + 1) (by omega)) (hd j (by omega)) (hanti j hj))
    (by
      intro j hj
      have hs : Real.sin (Real.pi * d j) ≠ 0 := by
        apply ne_of_gt
        apply Real.sin_pos_of_pos_of_lt_pi
        · exact mul_pos Real.pi_pos (hd j hj).1
        · nlinarith [Real.pi_pos, (hd j hj).2]
      have he : Real.pi * f (j + 1) = Real.pi * f j + Real.pi * d j := by
        rw [hstep j hj]
        ring
      rw [he]
      exact inversePhase_mul_increment hs (Real.pi * f j))
  convert h using 1
  field_simp

lemma unitPhase_int_pi (m : ℤ) : unitPhase (Real.pi * (m : ℝ)) = 1 := by
  unfold unitPhase
  have he : ((2 * (Real.pi * (m : ℝ)) : ℝ) : ℂ) * Complex.I =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
  rw [he, Complex.exp_int_mul_two_pi_mul_I]

lemma unitPhase_add_int_pi (θ : ℝ) (m : ℤ) :
    unitPhase (θ + Real.pi * (m : ℝ)) = unitPhase θ := by
  rw [unitPhase_add, unitPhase_int_pi, mul_one]

lemma unitPhase_pi_sub_int (x : ℝ) (m : ℤ) :
    unitPhase (Real.pi * (x - (m : ℝ))) = unitPhase (Real.pi * x) := by
  have he : Real.pi * (x - (m : ℝ)) = Real.pi * x + Real.pi * ((-m : ℤ) : ℝ) := by
    push_cast
    ring
  rw [he, unitPhase_add_int_pi]

/-- The first-derivative estimate on any fixed integer cell of increments. -/
theorem exponential_first_derivative_int_cell (f d : ℕ → ℝ) (n : ℕ) (m : ℤ) (β : ℝ)
    (hβ : 0 < β) (hstep : ∀ j ≤ n, f (j + 1) = f j + d j)
    (hbounds : ∀ j ≤ n, (m : ℝ) + β ≤ d j ∧ d j ≤ (m : ℝ) + 1 - β)
    (hmono : (∀ j < n, d j ≤ d (j + 1)) ∨ (∀ j < n, d (j + 1) ≤ d j)) :
    ‖∑ j ∈ Finset.range (n + 1), unitPhase (Real.pi * f j)‖ ≤ 1 / β := by
  let g : ℕ → ℝ := fun j => f j - (j : ℝ) * m
  let e : ℕ → ℝ := fun j => d j - m
  have h := exponential_first_derivative_bound g e n β hβ
    (by
      intro j hj
      dsimp [g, e]
      rw [hstep j hj]
      push_cast
      ring)
    (by
      intro j hj
      obtain ⟨hl, hu⟩ := hbounds j hj
      dsimp [e]
      constructor <;> linarith)
    (by
      rcases hmono with hm | hm
      · left
        intro j hj
        exact sub_le_sub_right (hm j hj) _
      · right
        intro j hj
        exact sub_le_sub_right (hm j hj) _)
  have heq (j : ℕ) : unitPhase (Real.pi * g j) = unitPhase (Real.pi * f j) := by
    have hh := unitPhase_pi_sub_int (f j) ((j : ℤ) * m)
    simpa only [g, Int.cast_mul, Int.cast_natCast] using hh
  simpa only [heq] using h

/-- Interval form for splitting an exponential sum into monotone integer cells. -/
theorem exponential_first_derivative_Ico (f d : ℕ → ℝ) (a b : ℕ) (m : ℤ) (β : ℝ)
    (hab : a < b) (hβ : 0 < β)
    (hstep : ∀ j ∈ Finset.Ico a b, f (j + 1) = f j + d j)
    (hbounds : ∀ j ∈ Finset.Ico a b,
      (m : ℝ) + β ≤ d j ∧ d j ≤ (m : ℝ) + 1 - β)
    (hmono : MonotoneOn d (Set.Ico a b) ∨ AntitoneOn d (Set.Ico a b)) :
    ‖∑ j ∈ Finset.Ico a b, unitPhase (Real.pi * f j)‖ ≤ 1 / β := by
  let n := b - a - 1
  have hn : n + 1 = b - a := by dsimp [n]; omega
  have hjmem (j : ℕ) (hj : j ≤ n) : a + j ∈ Finset.Ico a b := by
    simp only [Finset.mem_Ico]
    dsimp [n] at hj
    omega
  have h := exponential_first_derivative_int_cell
    (fun j => f (a + j)) (fun j => d (a + j)) n m β hβ
    (by
      intro j hj
      simpa only [Nat.add_assoc] using hstep (a + j) (hjmem j hj))
    (fun j hj => hbounds (a + j) (hjmem j hj))
    (by
      rcases hmono with hm | hm
      · left
        intro j hj
        exact hm (Finset.mem_Ico.mp (hjmem j (by omega)))
          (Finset.mem_Ico.mp (hjmem (j + 1) (by omega))) (by omega)
      · right
        intro j hj
        exact hm (Finset.mem_Ico.mp (hjmem j (by omega)))
          (Finset.mem_Ico.mp (hjmem (j + 1) (by omega))) (by omega))
  rw [Finset.sum_Ico_eq_sum_range]
  simpa only [hn] using h

end Problem337

end

end OAI

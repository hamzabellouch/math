import Mathlib

namespace OAI
open scoped BigOperators

namespace Problem337

/-- The natural-number ceiling algorithm, including its least nonnegative residue. -/
theorem nat_ceiling_residue (N u : ℕ) (hN : 0 < N) (hu : 0 < u) :
    ∃ z h : ℕ, 0 < z ∧ h < u ∧ N + h = u * z := by
  let z := (N - 1) / u + 1
  let r := (N - 1) % u
  let h := u - (r + 1)
  have hr : r < u := Nat.mod_lt _ hu
  have hdiv : u * ((N - 1) / u) + r = N - 1 := Nat.div_add_mod _ _
  have hh : h + (r + 1) = u := Nat.sub_add_cancel (by omega)
  have hNpred : N - 1 + 1 = N := by omega
  refine ⟨z, h, Nat.succ_pos _, by omega, ?_⟩
  dsimp [z]
  nlinarith

/-- The division step underlying both the terminal and backward numerator descent. -/
theorem residue_step_identity (M Q u t z h : ℕ)
    (hM : 0 < M) (hQ : 0 < Q) (ht : 0 < t) (hz : 0 < z)
    (htM : t ∣ M) (hres : Q * t + h = u * z) :
    (u : ℚ) / (M * Q : ℕ) =
      (1 : ℚ) / ((M / t) * z : ℕ) +
        (1 : ℚ) / z * ((h : ℚ) / (M * Q : ℕ)) := by
  have hMt : M / t * t = M := Nat.div_mul_cancel htM
  have hMtpos : 0 < M / t := by nlinarith
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have htq : (0 : ℚ) < t := by exact_mod_cast ht
  have hzq : (0 : ℚ) < z := by exact_mod_cast hz
  have hMtq : (0 : ℚ) < (M / t : ℕ) := by exact_mod_cast hMtpos
  have heq : ((M / t : ℕ) : ℚ) * t = M := by exact_mod_cast hMt
  have hresq : (Q : ℚ) * t + h = (u : ℚ) * z := by exact_mod_cast hres
  push_cast
  field_simp
  nlinarith

/-- Rescale an arbitrary positive unit-fraction list by a positive integer. -/
theorem unit_fraction_list_scale {k : ℕ} (n : Fin k → ℕ) (z : ℕ)
    (hn : ∀ i, 0 < n i) (hz : 0 < z) :
    (∀ i, 0 < z * n i) ∧
      (∑ i : Fin k, (1 : ℚ) / (z * n i : ℕ)) =
        (1 : ℚ) / z * (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) := by
  refine ⟨fun i => Nat.mul_pos hz (hn i), ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  rw [one_div_mul_one_div]

/-- Adjoining the unit fraction produced by a residue step lifts any expansion
of the smaller numerator. Repeated denominators are deliberately permitted. -/
theorem residue_step_list {k : ℕ} (M Q u t z h : ℕ)
    (hM : 0 < M) (hQ : 0 < Q) (ht : 0 < t) (hz : 0 < z)
    (htM : t ∣ M) (hres : Q * t + h = u * z)
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = (h : ℚ) / (M * Q : ℕ)) :
    ∃ n' : Fin (k + 1) → ℕ, (∀ i, 0 < n' i) ∧
      (∑ i : Fin (k + 1), (1 : ℚ) / (n' i : ℚ)) = (u : ℚ) / (M * Q : ℕ) := by
  have hMt : M / t * t = M := Nat.div_mul_cancel htM
  have hMtpos : 0 < M / t := by nlinarith
  obtain ⟨hpos, hscale⟩ := unit_fraction_list_scale n z hn hz
  refine ⟨Fin.cons ((M / t) * z) (fun i => z * n i), ?_, ?_⟩
  · intro i
    exact Fin.cases (Nat.mul_pos hMtpos hz) hpos i
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hscale, hsum]
    exact (residue_step_identity M Q u t z h hM hQ ht hz htM hres).symm

/-- Passing from a smaller denominator factor to a divisible larger one only
scales all unit denominators, and does not add terms. -/
theorem unit_fraction_list_change_factor {k : ℕ} (M Q Qnext h : ℕ)
    (hM : 0 < M) (hQ : 0 < Q) (hQnext : 0 < Qnext) (hdiv : Qnext ∣ Q)
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) =
      (h : ℚ) / (M * Qnext : ℕ)) :
    ∃ n' : Fin k → ℕ, (∀ i, 0 < n' i) ∧
      (∑ i : Fin k, (1 : ℚ) / (n' i : ℚ)) = (h : ℚ) / (M * Q : ℕ) := by
  have hfac : Q / Qnext * Qnext = Q := Nat.div_mul_cancel hdiv
  have hfacpos : 0 < Q / Qnext := by nlinarith
  obtain ⟨hpos, hscale⟩ := unit_fraction_list_scale n (Q / Qnext) hn hfacpos
  refine ⟨fun i => (Q / Qnext) * n i, hpos, ?_⟩
  rw [hscale, hsum]
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hQnextq : (0 : ℚ) < Qnext := by exact_mod_cast hQnext
  have hfacq : (0 : ℚ) < (Q / Qnext : ℕ) := by exact_mod_cast hfacpos
  have heq : ((Q / Qnext : ℕ) : ℚ) * Qnext = Q := by exact_mod_cast hfac
  push_cast
  field_simp
  nlinarith

/-- The full backward step, allowing the denominator factor to change by
an integer divisor between adjacent levels. -/
theorem residue_step_list_change_factor {k : ℕ} (M Q Qnext u t z h : ℕ)
    (hM : 0 < M) (hQ : 0 < Q) (hQnext : 0 < Qnext)
    (ht : 0 < t) (hz : 0 < z) (htM : t ∣ M) (hdiv : Qnext ∣ Q)
    (hres : Q * t + h = u * z)
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) =
      (h : ℚ) / (M * Qnext : ℕ)) :
    ∃ n' : Fin (k + 1) → ℕ, (∀ i, 0 < n' i) ∧
      (∑ i : Fin (k + 1), (1 : ℚ) / (n' i : ℚ)) = (u : ℚ) / (M * Q : ℕ) := by
  obtain ⟨n', hn', hsum'⟩ :=
    unit_fraction_list_change_factor M Q Qnext h hM hQ hQnext hdiv n hn hsum
  exact residue_step_list M Q u t z h hM hQ ht hz htM hres n' hn' hsum'

/-- Every positive unit fraction in a list of total less than one has
an integer denominator at least two. -/
theorem unit_fraction_denominators_two_of_sum_lt_one {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) < 1) :
    ∀ i, 2 ≤ n i := by
  intro i
  have hle : (1 : ℚ) / n i ≤ ∑ j : Fin k, (1 : ℚ) / n j :=
    Finset.single_le_sum (f := fun j : Fin k => (1 : ℚ) / n j) (fun j _ => by positivity) (Finset.mem_univ i)
  have hlt : (1 : ℚ) / n i < 1 := lt_of_le_of_lt hle hsum
  by_contra h
  have hni : n i = 1 := by have := hn i; omega
  simp [hni] at hlt

end Problem337

end OAI

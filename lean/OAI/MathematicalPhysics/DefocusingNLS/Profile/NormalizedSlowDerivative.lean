import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowHigherDerivatives

namespace OAI

/-! # The differential recurrence of the normalized outgoing solution -/

open Filter Topology

namespace DefocusingNLS

noncomputable def normalizedSlowSolution (q : ℂ) (m : ℕ) (x : ℂ) : ℂ :=
  x ^ q * regularizedSlowSolution q m x

theorem hasDerivAt_normalizedSlowSolution (q : ℂ) (m : ℕ) (x : ℂ)
    (hq : -1 < q.re) (hx : 0 ≤ x.re) (hx0 : x ≠ 0) :
    HasDerivAt (normalizedSlowSolution q m)
      (-q * ((m : ℂ) - 1 - q) / x ^ 2 * normalizedSlowSolution (q + 1) m x) x := by
  have hslit : x ∈ Complex.slitPlane := by
    rcases hx.eq_or_lt with hr | hr
    · apply Complex.mem_slitPlane_iff.mpr
      right
      intro hi
      exact hx0 (Complex.ext hr.symm hi)
    · exact Complex.mem_slitPlane_iff.mpr (Or.inl hr)
  have hp := (hasDerivAt_id x).cpow_const (c := q) hslit
  have hh := hasDerivAt_regularizedSlowSolution_shift_closed q m x hq hx hx0
  have hc := regularizedSlowSolution_contiguous q m x hq hx hx0
  have he : x ^ (q + 1) = x ^ (q - 1) * x ^ (2 : ℕ) := by
    calc
      x ^ (q + 1) = x ^ ((q - 1) + 2) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hx0, Complex.cpow_two]
  have he1 : x ^ q = x ^ (q - 1) * x := by
    calc
      x ^ q = x ^ ((q - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
  convert! hp.mul hh using 1
  simp only [normalizedSlowSolution, id_eq, he, he1, mul_one]
  rw [hc]
  field_simp
  ring

/-- The normalized solution is uniformly bounded for large arguments in the
closed right half-plane, including the two imaginary rays. -/
theorem normalizedSlowSolution_bounded (q : ℂ) (m : ℕ) (hq : -1 < q.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, 0 ≤ x.re → 1 ≤ ‖x‖ →
      ‖normalizedSlowSolution q m x‖ ≤ C := by
  obtain ⟨A, hA, hb⟩ := regularizedSlowSolution_first_remainder q m hq
  refine ⟨A + 1, by linarith, ?_⟩
  intro x hx hn
  calc
    ‖normalizedSlowSolution q m x‖ ≤ ‖normalizedSlowSolution q m x - 1‖ + 1 := by
      simpa only [norm_one] using norm_le_norm_sub_add (normalizedSlowSolution q m x) 1
    _ ≤ A / ‖x‖ + 1 := add_le_add (hb x hx hn) le_rfl
    _ ≤ A + 1 := add_le_add (div_le_self hA hn) le_rfl

end DefocusingNLS

end OAI

import Mathlib

namespace OAI
noncomputable section

namespace Problem337.MinorArc

/-- A closed major arc about a reduced rational, at Dirichlet scale `N`. -/
def arc (N : ℕ) (r : ℚ) : Set ℝ :=
  {x | |x - (r : ℝ)| ≤ 1 / ((r.den : ℝ) * N)}

/-- The union of major arcs with reduced denominator at most `Q`.
The rational parameter retains coprimality without a separate hypothesis. -/
def majorArcs (Q N : ℕ) : Set ℝ :=
  {x | ∃ r : ℚ, r.den ≤ Q ∧ x ∈ arc N r}

/-- Dirichlet approximation supplies a reduced rational with bounded denominator. -/
theorem exists_dirichlet_approximation (x : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ r : ℚ, r.den ≤ N ∧ x ∈ arc N r := by
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le x hN
  refine ⟨r, hden, hr.trans ?_⟩
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply one_div_le_one_div_of_le (mul_pos hd hn)
  nlinarith

/-- Outside the major arcs, Dirichlet's denominator is in the minor-arc window. -/
theorem exists_minor_approximation (x : ℝ) {Q N : ℕ} (hN : 0 < N)
    (hx : x ∉ majorArcs Q N) :
    ∃ r : ℚ, Q < r.den ∧ r.den ≤ N ∧ x ∈ arc N r := by
  obtain ⟨r, hrN, hxr⟩ := exists_dirichlet_approximation x hN
  refine ⟨r, ?_, hrN, hxr⟩
  by_contra h
  exact hx ⟨r, Nat.le_of_not_gt h, hxr⟩

/-- The Dirichlet error is also at most the reciprocal square of the
reduced denominator, the form used by rational-approximation block estimates. -/
theorem arc_error_le_den_sq {N : ℕ} {r : ℚ} {x : ℝ}
    (hrN : r.den ≤ N) (hx : x ∈ arc N r) :
    |x - (r : ℝ)| ≤ 1 / (r.den : ℝ) ^ 2 := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hn : (r.den : ℝ) ≤ N := by exact_mod_cast hrN
  apply hx.trans
  apply one_div_le_one_div_of_le (sq_pos_of_pos hd)
  nlinarith

/-- An explicit coprime numerator/denominator version of minor-arc extraction. -/
theorem exists_minor_coprime_fraction (x : ℝ) {Q N : ℕ} (hN : 0 < N)
    (hx : x ∉ majorArcs Q N) :
    ∃ a : ℤ, ∃ q : ℕ, Q < q ∧ q ≤ N ∧ 0 < q ∧
      IsCoprime a (q : ℤ) ∧
      |x - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * N) ∧
      |x - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
  obtain ⟨r, hQr, hrN, hxr⟩ := exists_minor_approximation x hN hx
  refine ⟨r.num, r.den, hQr, hrN, r.den_pos, r.isCoprime_num_den, ?_, ?_⟩
  · simpa only [arc, Set.mem_ofPred_eq, Rat.cast_def] using hxr
  · simpa only [Rat.cast_def] using arc_error_le_den_sq hrN hxr

/-- Distinct reduced rationals have the usual reciprocal-product separation. -/
theorem rational_separation {r s : ℚ} (hrs : r ≠ s) :
    1 / ((r.den : ℝ) * s.den) ≤ |(r : ℝ) - s| := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have he : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hnum : r.num * (s.den : ℤ) - s.num * (r.den : ℤ) ≠ 0 := by
    intro h
    exact hrs (Rat.eq_iff_mul_eq_mul.mpr (sub_eq_zero.mp h))
  have hnum1 : (1 : ℝ) ≤ |(r.num : ℝ) * s.den - (s.num : ℝ) * r.den| := by
    exact_mod_cast Int.one_le_abs hnum
  rw [Rat.cast_def, Rat.cast_def, div_sub_div _ _ hd.ne' he.ne', abs_div,
    abs_of_pos (mul_pos hd he)]
  simpa only [mul_comm] using
    div_le_div_of_nonneg_right hnum1 (mul_nonneg hd.le he.le)

/-- Two Dirichlet-scale major arcs cannot overlap when their denominator sum
is smaller than the approximation scale. -/
theorem arc_disjoint {r s : ℚ} (hrs : r ≠ s) {N : ℕ}
    (hN : r.den + s.den < N) : Disjoint (arc N r) (arc N s) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have he : (0 : ℝ) < s.den := by exact_mod_cast s.den_pos
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hsum : (r.den : ℝ) + s.den < N := by exact_mod_cast hN
  have hsep := rational_separation hrs
  have htri := abs_sub_le (r : ℝ) x (s : ℝ)
  have hx' : |(r : ℝ) - x| ≤ 1 / ((r.den : ℝ) * N) := by
    simpa only [arc, Set.mem_ofPred_eq, abs_sub_comm] using hx
  have hy' : |x - (s : ℝ)| ≤ 1 / ((s.den : ℝ) * N) := hy
  have hsmall : 1 / ((r.den : ℝ) * N) + 1 / ((s.den : ℝ) * N) <
      1 / ((r.den : ℝ) * s.den) := by
    field_simp
    nlinarith
  linarith

/-- In the standard window `2Q < N`, all distinct major-arc centers are disjoint. -/
theorem major_arc_unique {Q N : ℕ} (hQN : 2 * Q < N) {x : ℝ}
    {r s : ℚ} (hr : r.den ≤ Q) (hs : s.den ≤ Q)
    (hxr : x ∈ arc N r) (hxs : x ∈ arc N s) : r = s := by
  by_contra hrs
  exact (Set.disjoint_left.mp (arc_disjoint hrs (by omega))) hxr hxs

/-- A nonintegral multiple of a reduced rational stays at least `1/q` from
any integer. This formulation is uniform in the chosen nearest integer. -/
theorem rational_multiple_separation (r : ℚ) (d k : ℤ)
    (hnd : ¬ (r.den : ℤ) ∣ d) :
    1 / (r.den : ℝ) ≤ |(r : ℝ) * d - k| := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hnum : r.num * d - k * (r.den : ℤ) ≠ 0 := by
    intro h
    apply hnd
    apply r.isCoprime_num_den.symm.dvd_of_dvd_mul_left
    rw [sub_eq_zero.mp h]
    exact dvd_mul_left _ _
  have hone : (1 : ℝ) ≤ |(r.num : ℝ) * d - k * r.den| := by
    exact_mod_cast Int.one_le_abs hnum
  have heq : (r : ℝ) * d - k =
      ((r.num : ℝ) * d - k * r.den) / r.den := by
    rw [Rat.cast_def]
    field_simp
  rw [heq, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right hone hd.le

/-- Rational approximation remains separated from integers over a half-length
block; this is the spacing input needed for irrational minor-arc block sums. -/
theorem perturbed_multiple_separation (r : ℚ) {x : ℝ} (d k : ℤ)
    (hx : |x - (r : ℝ)| ≤ 1 / (r.den : ℝ) ^ 2)
    (hnd : ¬ (r.den : ℤ) ∣ d)
    (hdsmall : |(d : ℝ)| ≤ (r.den : ℝ) / 2) :
    1 / (2 * (r.den : ℝ)) ≤ |x * d - k| := by
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have herr : |(r : ℝ) * d - x * d| ≤ 1 / (2 * (r.den : ℝ)) := by
    rw [← sub_mul, abs_mul, abs_sub_comm]
    calc
      |x - (r : ℝ)| * |(d : ℝ)| ≤
          (1 / (r.den : ℝ) ^ 2) * ((r.den : ℝ) / 2) :=
        mul_le_mul hx hdsmall (abs_nonneg _) (by positivity)
      _ = 1 / (2 * (r.den : ℝ)) := by field_simp
  have hsep := rational_multiple_separation r d k hnd
  have htri := abs_sub_le ((r : ℝ) * d) (x * d) (k : ℝ)
  have hid : 1 / (r.den : ℝ) = 2 * (1 / (2 * (r.den : ℝ))) := by ring
  linarith

/-- A nonzero integer shorter than a positive modulus is not divisible by it. -/
theorem not_dvd_of_abs_lt {q : ℕ} {d : ℤ} (hd : d ≠ 0)
    (hlt : |(d : ℝ)| < (q : ℝ)) : ¬ (q : ℤ) ∣ d := by
  intro hdiv
  have hle : q ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hd)
    (Int.natCast_dvd.mp hdiv)
  have hleZ : (q : ℤ) ≤ |d| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hle
  have hle' : (q : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast hleZ
  exact (not_lt_of_ge hle') hlt

/-- Distinct phases in a half-denominator block are uniformly separated
modulo one, including after a Dirichlet-sized perturbation. -/
theorem perturbed_block_separation (r : ℚ) {x : ℝ} (m n k : ℤ)
    (hx : |x - (r : ℝ)| ≤ 1 / (r.den : ℝ) ^ 2)
    (hmn : m ≠ n) (hblock : |(m : ℝ) - n| ≤ (r.den : ℝ) / 2) :
    1 / (2 * (r.den : ℝ)) ≤ |x * m - x * n - k| := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hsmall : |((m - n : ℤ) : ℝ)| ≤ (r.den : ℝ) / 2 := by
    simpa only [Int.cast_sub] using hblock
  have hnd : ¬ (r.den : ℤ) ∣ m - n :=
    not_dvd_of_abs_lt (sub_ne_zero.mpr hmn) (by linarith)
  simpa only [Int.cast_sub, mul_sub] using
    perturbed_multiple_separation r (m - n) k hx hnd hsmall

/-- The same separation in the nearest-integer distance convention. -/
theorem perturbed_block_round_separation (r : ℚ) {x : ℝ} (m n : ℤ)
    (hx : |x - (r : ℝ)| ≤ 1 / (r.den : ℝ) ^ 2)
    (hmn : m ≠ n) (hblock : |(m : ℝ) - n| ≤ (r.den : ℝ) / 2) :
    1 / (2 * (r.den : ℝ)) ≤
      |(x * m - x * n) - round (x * m - x * n)| := by
  exact perturbed_block_separation r m n _ hx hmn hblock

end Problem337.MinorArc

end

end OAI

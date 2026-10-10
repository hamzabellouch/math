import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedEnergy

namespace OAI

/-! # Scale-uniform frequency gain for the ordered torus commutator -/

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def expandingOrderedFactor (a L : ℝ) (N : ℕ) (n : frequencyLattice) : ℝ :=
  (2 * Real.pi) ^ 6 * L ^ (6 - (N : ℝ)) / expandingSobolevWeight a N L n

theorem expandingOrderedFactor_nonneg (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (n : frequencyLattice) : 0 ≤ expandingOrderedFactor a L N n := by
  unfold expandingOrderedFactor
  exact div_nonneg (mul_nonneg (by positivity) (by positivity))
    (expandingSobolevWeight_pos a N L hL n).le

theorem expandingOrderedFactor_radial_le (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (n : frequencyLattice) : expandingOrderedFactor a L N n * ‖n‖ ^ N ≤ 1 := by
  have he := expandingOrderedMultiplier_sq_sum a L N hL n
  have hs : (∑ j : Fin N → Fin 12, ‖expandingOrderedMultiplier a L N j n‖ ^ 2) =
      (expandingOrderedFactor a L N n * ‖n‖ ^ N) ^ 2 := by
    simp only [expandingOrderedMultiplier, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    rw [← Finset.mul_sum, homogeneousOrderedSymbol_sq_sum, Submodule.norm_coe]
    dsimp only [expandingOrderedFactor]
    ring
  rw [hs] at he
  have hl := (expandingLowFraction_bounds a N L hL n).1
  nlinarith

noncomputable def expandingOrderedDifference (a L : ℝ) (N : ℕ)
    (j : Fin N → Fin 12) (m n : frequencyLattice) : ℂ :=
  (expandingOrderedFactor a L N n : ℂ) *
    (homogeneousOrderedSymbol N j (n + m) - homogeneousOrderedSymbol N j n)

theorem expandingOrderedDifference_high (a L R : ℝ) (N : ℕ)
    (hL : 1 ≤ L) (hR : 1 ≤ R) (j : Fin (N + 1) → Fin 12)
    (m n : frequencyLattice) (hn : R * L ≤ ‖n‖) :
    ‖expandingOrderedDifference a L (N + 1) j m n‖ ≤
      ((N + 1 : ℕ) / R) * (‖m‖ / L) * (2 + ‖m‖ / L) ^ N := by
  have hLp : 0 < L := by linarith
  have hRp : 0 < R := by linarith
  have hnL : L ≤ ‖n‖ := (le_mul_of_one_le_left hLp.le hR).trans hn
  have hnn : 0 < ‖n‖ := hLp.trans_le hnL
  have hsum : ‖(n + m : frequencyLattice)‖ + ‖n‖ ≤
      (2 + ‖m‖ / L) * ‖n‖ := by
    have h := mul_le_mul_of_nonneg_left hnL (div_nonneg (norm_nonneg m) hLp.le)
    have he : (‖m‖ / L) * L = ‖m‖ := div_mul_cancel₀ _ hLp.ne'
    rw [he] at h
    nlinarith [norm_add_le n m]
  have hd := homogeneousOrderedSymbol_sub_le N j (n + m : frequencyLattice) n
  have hdif : ((n + m : frequencyLattice) : E) - (n : E) = (m : E) := by
    change (n : E) + (m : E) - (n : E) = (m : E)
    abel
  rw [hdif, Submodule.norm_coe, Submodule.norm_coe, Submodule.norm_coe] at hd
  have hp : (‖n + m‖ + ‖n‖) ^ N ≤ (2 + ‖m‖ / L) ^ N * ‖n‖ ^ N := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hsum N
  have hfac := expandingOrderedFactor_radial_le a L (N + 1) hL n
  have hgain : expandingOrderedFactor a L (N + 1) n * ‖n‖ ^ N ≤ (R * L)⁻¹ := by
    rw [← one_div (R * L)]
    apply (le_div_iff₀ (mul_pos hRp hLp)).mpr
    calc
      _ ≤ expandingOrderedFactor a L (N + 1) n * ‖n‖ ^ N * ‖n‖ :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg (expandingOrderedFactor_nonneg _ _ _ hL _) (by positivity))
      _ = expandingOrderedFactor a L (N + 1) n * ‖n‖ ^ (N + 1) := by rw [pow_succ]; ring
      _ ≤ 1 := hfac
  rw [expandingOrderedDifference, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (expandingOrderedFactor_nonneg _ _ _ hL _)]
  calc
    _ ≤ expandingOrderedFactor a L (N + 1) n *
        ((N + 1 : ℕ) * ‖m‖ * ((2 + ‖m‖ / L) ^ N * ‖n‖ ^ N)) :=
      mul_le_mul_of_nonneg_left (hd.trans (mul_le_mul_of_nonneg_left hp (by positivity)))
        (expandingOrderedFactor_nonneg _ _ _ hL _)
    _ = ((N + 1 : ℕ) * ‖m‖ * (2 + ‖m‖ / L) ^ N) *
        (expandingOrderedFactor a L (N + 1) n * ‖n‖ ^ N) := by ring
    _ ≤ ((N + 1 : ℕ) * ‖m‖ * (2 + ‖m‖ / L) ^ N) * (R * L)⁻¹ :=
      mul_le_mul_of_nonneg_left hgain (by positivity)
    _ = _ := by rw [mul_inv_rev]; simp only [div_eq_mul_inv]; ring

end DefocusingNLS

end OAI

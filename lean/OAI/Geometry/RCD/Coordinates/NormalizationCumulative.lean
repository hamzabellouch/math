import OAI.Geometry.RCD.Heat.HeatCumulative

namespace OAI

/-! # Finite families of changing mean normalizations -/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Summing the proved inverse-normalization estimate over at most `J`
centers per scale preserves its weighted heat total. -/
theorem inverse_normalization_errors_sum_le
    (Q : ℕ → E ≃L[ℝ] E) (R : ℕ → ι → E ≃L[ℝ] E)
    (F : ℕ → E →L[ℝ] E) (s : ℕ → Finset ι)
    (hQ : ∀ i, (Q i : E →L[ℝ] E).IsPositive)
    (hR : ∀ i y, y ∈ s i → (R i y : E →L[ℝ] E).IsPositive)
    (hF : ∀ i, (F i).IsPositive) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hcompare : ∀ i y, y ∈ s i → ∀ v, c * ⟪v, Q i v⟫_ℝ ≤ ⟪v, R i y v⟫_ℝ)
    (hbilinear : ∀ i y, y ∈ s i → ∀ u v,
      ⟪v, ((R i y : E →L[ℝ] E) - (Q i : E →L[ℝ] E)) u⟫_ℝ ^ 2 ≤
        (C * ⟪u, F i u⟫_ℝ) * ⟪v, Q i v⟫_ℝ)
    (J : ℕ) (hcard : ∀ i, (s i).card ≤ J) (xi : E) (k : ℕ) :
    (∑ i ∈ Finset.range k, ∑ y ∈ s i,
      ⟪(R i y).symm xi - (Q i).symm xi,
        Q i ((R i y).symm xi - (Q i).symm xi)⟫_ℝ) ≤
      (J : ℝ) * (C / c ^ 2) *
        ∑ i ∈ Finset.range k, ⟪(Q i).symm xi, F i ((Q i).symm xi)⟫_ℝ := by
  have hscale : 0 ≤ C / c ^ 2 := div_nonneg hC (sq_nonneg c)
  calc
    _ ≤ ∑ i ∈ Finset.range k, (J : ℝ) * (C / c ^ 2) *
        ⟪(Q i).symm xi, F i ((Q i).symm xi)⟫_ℝ := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ y ∈ s i, (C / c ^ 2) * ⟪(Q i).symm xi, F i ((Q i).symm xi)⟫_ℝ :=
          Finset.sum_le_sum fun y hy => inverse_normalization_error_le
            (Q i) (R i y) (hQ i) (hR i y hy) (F i) (hF i) hc hC
            (hcompare i y hy) (hbilinear i y hy) xi
        _ = ((s i).card : ℝ) * ((C / c ^ 2) * ⟪(Q i).symm xi, F i ((Q i).symm xi)⟫_ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (J : ℝ) * ((C / c ^ 2) * ⟪(Q i).symm xi, F i ((Q i).symm xi)⟫_ℝ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard i)
            (mul_nonneg hscale ((hF i).inner_nonneg_right _))
        _ = _ := by ring
    _ = _ := by rw [Finset.mul_sum]

/-- A small positive mass form charges a normalization error by at most
`epsilon` times its energy in the reference metric. -/
theorem normalization_mass_errors_sum_le
    (Q : ℕ → E →L[ℝ] E) (C : ℕ → ι → E →L[ℝ] E)
    (s : ℕ → Finset ι) (e : ℕ → ι → E) {epsilon : ℝ}
    (hsmall : ∀ i y, y ∈ s i → ∀ v, ⟪v, C i y v⟫_ℝ ≤ epsilon * ⟪v, Q i v⟫_ℝ)
    (k : ℕ) :
    (∑ i ∈ Finset.range k, ∑ y ∈ s i, ⟪e i y, C i y (e i y)⟫_ℝ) ≤
      epsilon * ∑ i ∈ Finset.range k, ∑ y ∈ s i, ⟪e i y, Q i (e i y)⟫_ℝ := by
  calc
    _ ≤ ∑ i ∈ Finset.range k, ∑ y ∈ s i, epsilon * ⟪e i y, Q i (e i y)⟫_ℝ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun y hy => hsmall i y hy (e i y)
    _ = _ := by simp only [Finset.mul_sum]

/-- Changing inverse normalization preserves the small pointwise mass bound. -/
theorem inverse_normalized_mass_le (Q R : E ≃L[ℝ] E)
    (hQ : (Q : E →L[ℝ] E).IsPositive) (hR : (R : E →L[ℝ] E).IsPositive)
    (D : E →L[ℝ] E) {c epsilon : ℝ} (hc : 0 < c) (hepsilon : 0 ≤ epsilon)
    (hcompare : ∀ v, c * ⟪v, Q v⟫_ℝ ≤ ⟪v, R v⟫_ℝ)
    (hsmall : ∀ v, ⟪v, D v⟫_ℝ ≤ epsilon * ⟪v, Q v⟫_ℝ) (xi : E) :
    ⟪R.symm xi, D (R.symm xi)⟫_ℝ ≤ epsilon / c ^ 2 * ⟪xi, Q.symm xi⟫_ℝ := by
  calc
    _ ≤ epsilon * ⟪R.symm xi, Q (R.symm xi)⟫_ℝ := hsmall _
    _ ≤ epsilon * (⟪xi, Q.symm xi⟫_ℝ / c ^ 2) :=
      mul_le_mul_of_nonneg_left (relative_inverse_bounds Q R hQ hR hc hcompare xi).2 hepsilon
    _ = _ := by ring

/-- The finite-family part of the cumulative comparison. Its inputs are
weighted totals and the central estimate proved from the heat decrements;
all changes of normalization and the reverse covering argument are proved
here. The vectors `z i y` may be the actual local inverse images. -/
theorem local_mass_cumulative_comparison
    (N : ℕ → E →L[ℝ] E) (C : ℕ → ι → E →L[ℝ] E)
    (s : ℕ → Finset ι) (theta : ℕ → ι → ℝ)
    (a : ℕ → E) (z : ℕ → ι → E)
    (hC : ∀ i y, y ∈ s i → (C i y).IsPositive)
    (htheta : ∀ i y, y ∈ s i → 0 ≤ theta i y)
    (hcover : ∀ i, ∃ y ∈ s i, theta i y = 1 ∧
      ∀ v, ⟪v, N i v⟫_ℝ ≤ ⟪v, C i y v⟫_ℝ)
    {H t U V K epsilon : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) (k : ℕ)
    (hupper : (∑ i ∈ Finset.range k, ∑ y ∈ s i, ⟪a i, C i y (a i)⟫_ℝ) ≤ U * H)
    (herror : (∑ i ∈ Finset.range k, ∑ y ∈ s i,
      ⟪z i y - a i, C i y (z i y - a i)⟫_ℝ) ≤ V * epsilon * H)
    (hcentral : H ≤ K * (t + ∑ i ∈ Finset.range k, ⟪a i, N i (a i)⟫_ℝ))
    (habsorb : 2 * K * V * epsilon ≤ 1 / 2) :
    (∑ i ∈ Finset.range k, ∑ y ∈ s i, ⟪z i y, C i y (z i y)⟫_ℝ) ≤
      2 * (U + V * epsilon) * H ∧
    H ≤ 2 * K * t + 4 * K *
      (∑ i ∈ Finset.range k, ∑ y ∈ s i, theta i y * ⟪z i y, C i y (z i y)⟫_ℝ) := by
  classical
  let err := ∑ i ∈ Finset.range k, ∑ y ∈ s i,
    ⟪z i y - a i, C i y (z i y - a i)⟫_ℝ
  let weighted := ∑ i ∈ Finset.range k, ∑ y ∈ s i,
    theta i y * ⟪z i y, C i y (z i y)⟫_ℝ
  have herr : err ≤ V * epsilon * H := herror
  constructor
  · have hp := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range k) =>
      Finset.sum_le_sum (fun y (hy : y ∈ s i) =>
        positive_form_add_le_two (hC i y hy) (a i) (z i y - a i)))
    simp only [add_sub_cancel, Finset.sum_add_distrib, ← Finset.mul_sum] at hp
    have hu := hupper
    change _ ≤ 2 * _ + 2 * err at hp
    nlinarith
  · have hpoint (i : ℕ) : ⟪a i, N i (a i)⟫_ℝ ≤
        2 * (∑ y ∈ s i, theta i y * ⟪z i y, C i y (z i y)⟫_ℝ) +
        2 * (∑ y ∈ s i, ⟪z i y - a i, C i y (z i y - a i)⟫_ℝ) := by
      obtain ⟨y, hy, hweight, hdom⟩ := hcover i
      have hmain : ⟪z i y, C i y (z i y)⟫_ℝ ≤
          ∑ j ∈ s i, theta i j * ⟪z i j, C i j (z i j)⟫_ℝ := by
        have hh := Finset.single_le_sum (fun j (hj : j ∈ s i) =>
          mul_nonneg (htheta i j hj) ((hC i j hj).inner_nonneg_right (z i j))) hy
        simpa only [hweight, one_mul] using hh
      have he : ⟪z i y - a i, C i y (z i y - a i)⟫_ℝ ≤
          ∑ j ∈ s i, ⟪z i j - a i, C i j (z i j - a i)⟫_ℝ :=
        Finset.single_le_sum (fun j (hj : j ∈ s i) =>
          (hC i j hj).inner_nonneg_right (z i j - a i)) hy
      have htwo := positive_form_add_le_two (hC i y hy) (z i y) (-(z i y - a i))
      have heq : z i y + -(z i y - a i) = a i := by abel
      rw [heq] at htwo
      simp only [map_neg, inner_neg_left, inner_neg_right, neg_neg] at htwo
      have hd := hdom (a i)
      linarith
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range k) => hpoint i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    change _ ≤ 2 * weighted + 2 * err at hs
    have hc := hcentral
    have hns := mul_le_mul_of_nonneg_left hs hK
    have he := mul_le_mul_of_nonneg_left herr (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK)
    have ha := mul_le_mul_of_nonneg_right habsorb hH
    nlinarith

end RegularPointCoordinates

end

end OAI

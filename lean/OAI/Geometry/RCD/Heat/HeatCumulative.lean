import OAI.Geometry.RCD.Coordinates.WeightedInverse
import OAI.Geometry.RCD.Coordinates.WeightedConvolution

namespace OAI

/-!
# Accumulating heat decrements in changing inverse metrics

All forms act on one fixed real inner product space. The hypotheses are local
heat envelopes, small one-step decrements, and slow metric growth. In particular,
neither the weighted total nor the cumulative comparison is an input.
-/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic-form version of the two-term Young inequality. -/
theorem positive_form_add_le_two {D : E →L[ℝ] E} (hD : D.IsPositive) (x y : E) :
    ⟪x + y, D (x + y)⟫_ℝ ≤ 2 * ⟪x, D x⟫_ℝ + 2 * ⟪y, D y⟫_ℝ := by
  have hp := hD.inner_nonneg_right (x - y)
  simp only [map_sub, map_add, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right] at hp ⊢
  linarith

/-- Inverse vectors telescope over every finite interval. -/
theorem inverse_vector_telescopes (Q : ℕ → E ≃L[ℝ] E) (xi : E)
    {j i : ℕ} (hji : j ≤ i) :
    (Q i).symm xi - (Q j).symm xi =
      ∑ l ∈ Finset.Ico j i,
        (((Q (l + 1)).symm : E →L[ℝ] E) - ((Q l).symm : E →L[ℝ] E)) xi := by
  simp only [sub_apply, ContinuousLinearEquiv.coe_coe]
  rw [Finset.sum_Ico_eq_sub _ hji,
    Finset.sum_range_sub (fun l => (Q l).symm xi) i,
    Finset.sum_range_sub (fun l => (Q l).symm xi) j]
  abel

/-- Slow growth transports the energy of inverse increments to an earlier
metric. The resulting lag factor is precisely the one used in the heat kernel
convolution. -/
theorem inverse_vector_interval_energy (Q : ℕ → E ≃L[ℝ] E)
    (hQ : ∀ i, (Q i : E →L[ℝ] E).IsPositive)
    (hdec : ∀ i, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)).IsPositive)
    (hsmall : ∀ i v, ⟪v, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)) v⟫_ℝ ≤
      (1 / 2 : ℝ) * ⟪v, Q i v⟫_ℝ)
    {G g : ℝ} (hG : 0 ≤ G) (hg : 1 ≤ g)
    (hgrowth : ∀ j l, j ≤ l → ∀ v, ⟪v, Q j v⟫_ℝ ≤ G * g ^ (l - j) * ⟪v, Q l v⟫_ℝ)
    (xi : E) {j i : ℕ} (hji : j ≤ i) :
    ⟪(Q i).symm xi - (Q j).symm xi,
      Q j ((Q i).symm xi - (Q j).symm xi)⟫_ℝ ≤
      G * (i - j : ℕ) * g ^ (i - j) *
        ∑ l ∈ Finset.Ico j i,
          ⟪xi, (((Q (l + 1)).symm : E →L[ℝ] E) - ((Q l).symm : E →L[ℝ] E)) xi⟫_ℝ := by
  let b : ℕ → E := fun l =>
    (((Q (l + 1)).symm : E →L[ℝ] E) - ((Q l).symm : E →L[ℝ] E)) xi
  have hb (l : ℕ) : 0 ≤ ⟪xi, b l⟫_ℝ :=
    (inverse_increment_isPositive (Q l) (Q (l + 1)) (hQ l) (hQ (l + 1)) (hdec l)).inner_nonneg_right xi
  have hterm (l : ℕ) (hl : l ∈ Finset.Ico j i) :
      ⟪b l, Q j (b l)⟫_ℝ ≤ G * g ^ (i - j) * ⟪xi, b l⟫_ℝ := by
    obtain ⟨hjl, hli⟩ := Finset.mem_Ico.mp hl
    have hs := inverse_increment_weighted_square_le (Q l) (Q (l + 1))
      (hQ l) (hQ (l + 1)) (hdec l) (hsmall l) xi
    change ⟪b l, Q l (b l)⟫_ℝ ≤ ⟪xi, b l⟫_ℝ at hs
    calc
      _ ≤ G * g ^ (l - j) * ⟪b l, Q l (b l)⟫_ℝ := hgrowth j l hjl (b l)
      _ ≤ G * g ^ (l - j) * ⟪xi, b l⟫_ℝ :=
        mul_le_mul_of_nonneg_left hs (mul_nonneg hG (pow_nonneg (by linarith) _))
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hg
          (Nat.sub_le_sub_right hli.le j)) hG) (hb l)
  rw [inverse_vector_telescopes Q xi hji]
  calc
    _ ≤ ((Finset.Ico j i).card : ℝ) * ∑ l ∈ Finset.Ico j i, ⟪b l, Q j (b l)⟫_ℝ :=
      positive_form_sum_le_card (Q j) (hQ j) _ b
    _ ≤ ((Finset.Ico j i).card : ℝ) *
        ∑ l ∈ Finset.Ico j i, (G * g ^ (i - j)) * ⟪xi, b l⟫_ℝ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg _)
    _ = _ := by rw [Nat.card_Ico, ← Finset.mul_sum]; ring

/-- Summing a moving-vector convolution introduces only the ordinary
geometric constant and the second lag moment. -/
theorem moving_form_convolution_le (Q N : ℕ → E →L[ℝ] E)
    (hN : ∀ i, (N i).IsPositive) (a : ℕ → E) (b : ℕ → ℝ)
    (hb : ∀ i, 0 ≤ b i) {epsilon beta G g : ℝ}
    (hepsilon : 0 ≤ epsilon) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1)
    (hG : 0 ≤ G) (hg : 0 ≤ g) (hbetag : beta * g < 1)
    (hsmall : ∀ i v, ⟪v, N i v⟫_ℝ ≤ epsilon * ⟪v, Q i v⟫_ℝ)
    (hinterval : ∀ j i, j ≤ i →
      ⟪a i - a j, Q j (a i - a j)⟫_ℝ ≤
        G * (i - j : ℕ) * g ^ (i - j) * ∑ l ∈ Finset.Ico j i, b l)
    (k : ℕ) :
    (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (i + 1),
      beta ^ (i - j) * ⟪a i, N j (a i)⟫_ℝ) ≤
      2 * (1 - beta)⁻¹ * (∑ j ∈ Finset.range k, ⟪a j, N j (a j)⟫_ℝ) +
        2 * epsilon * G * geometricIntervalConstant (beta * g) * ∑ l ∈ Finset.range k, b l := by
  have hpoint (i j : ℕ) (hji : j ≤ i) :
      beta ^ (i - j) * ⟪a i, N j (a i)⟫_ℝ ≤
        2 * (beta ^ (i - j) * ⟪a j, N j (a j)⟫_ℝ) +
        2 * epsilon * G * (((i - j : ℕ) : ℝ) * (beta * g) ^ (i - j) *
          ∑ l ∈ Finset.Ico j i, b l) := by
    have hy := positive_form_add_le_two (hN j) (a j) (a i - a j)
    rw [add_sub_cancel] at hy
    have hs := hsmall j (a i - a j)
    have hi := mul_le_mul_of_nonneg_left (hinterval j i hji) hepsilon
    have hp := mul_le_mul_of_nonneg_left (by linarith :
      ⟪a i, N j (a i)⟫_ℝ ≤ 2 * ⟪a j, N j (a j)⟫_ℝ +
        2 * epsilon * (G * (i - j : ℕ) * g ^ (i - j) * ∑ l ∈ Finset.Ico j i, b l))
      (pow_nonneg hbeta (i - j))
    convert hp using 1
    simp only [mul_pow]
    ring
  calc
    _ ≤ ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (i + 1),
        (2 * (beta ^ (i - j) * ⟪a j, N j (a j)⟫_ℝ) +
          2 * epsilon * G * (((i - j : ℕ) : ℝ) * (beta * g) ^ (i - j) *
            ∑ l ∈ Finset.Ico j i, b l)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j hj
      exact hpoint i j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = 2 * (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (i + 1),
        beta ^ (i - j) * ⟪a j, N j (a j)⟫_ℝ) +
        2 * epsilon * G * (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (i + 1),
          ((i - j : ℕ) : ℝ) * (beta * g) ^ (i - j) *
            ∑ l ∈ Finset.Ico j i, b l) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * ((1 - beta)⁻¹ * (∑ j ∈ Finset.range k, ⟪a j, N j (a j)⟫_ℝ)) +
        2 * epsilon * G * (geometricIntervalConstant (beta * g) *
          ∑ l ∈ Finset.range k, b l) := add_le_add
      (mul_le_mul_of_nonneg_left
        (weighted_geometric_stationary_convolution_le k _
          (fun j => (hN j).inner_nonneg_right _) hbeta hbeta1) (by norm_num))
      (mul_le_mul_of_nonneg_left
        (weighted_geometric_interval_convolution_le k b hb
          (mul_nonneg hbeta hg) hbetag) (by positivity))
    _ = _ := by ring

omit [InnerProductSpace ℝ E] in
/-- A geometric background contribution remains bounded after applying
inverse metrics whose squared norms have slower exponential growth. -/
theorem inverse_background_sum_le (a : ℕ → E) (xi : E)
    {beta g K : ℝ} (hbeta : 0 ≤ beta) (hg : 0 ≤ g) (hK : 0 ≤ K)
    (hbg : beta * g < 1)
    (ha : ∀ i, ‖a i‖ ^ 2 ≤ K * g ^ i * ‖xi‖ ^ 2) (k : ℕ) :
    (∑ i ∈ Finset.range k, beta ^ i * ‖a i‖ ^ 2) ≤
      K * (1 - beta * g)⁻¹ * ‖xi‖ ^ 2 := by
  have hs : Summable (fun i : ℕ => (beta * g) ^ i) :=
    summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg (mul_nonneg hbeta hg)])
  have hsum : (∑ i ∈ Finset.range k, (beta * g) ^ i) ≤ (1 - beta * g)⁻¹ := by
    have hh := hs.sum_le_tsum (Finset.range k) (fun i _ => pow_nonneg (mul_nonneg hbeta hg) i)
    rwa [tsum_geometric_of_norm_lt_one
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hbeta hg)] using hbg)] at hh
  calc
    _ ≤ ∑ i ∈ Finset.range k, beta ^ i * (K * g ^ i * ‖xi‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha i) (pow_nonneg hbeta i)
    _ = K * (∑ i ∈ Finset.range k, (beta * g) ^ i) * ‖xi‖ ^ 2 := by
      simp only [mul_pow, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hK) (sq_nonneg _)

/-- Exact scalar telescope of the inverse increments. -/
theorem inverse_energy_telescopes (Q : ℕ → E ≃L[ℝ] E) (xi : E) (k : ℕ) :
    (∑ i ∈ Finset.range k,
      ⟪xi, (((Q (i + 1)).symm : E →L[ℝ] E) - ((Q i).symm : E →L[ℝ] E)) xi⟫_ℝ) =
      ⟪xi, (Q k).symm xi⟫_ℝ - ⟪xi, (Q 0).symm xi⟫_ℝ := by
  simp only [sub_apply, ContinuousLinearEquiv.coe_coe, inner_sub_right]
  exact Finset.sum_range_sub (fun i => ⟪xi, (Q i).symm xi⟫_ℝ) k

/-- The heat envelope implies a weighted total estimate at the moving
inverse vectors. This is proved before using either cumulative comparison. -/
theorem inverse_heat_envelope_sum_le (Q : ℕ → E ≃L[ℝ] E)
    (N F : ℕ → E →L[ℝ] E)
    (hQ : ∀ i, (Q i : E →L[ℝ] E).IsPositive)
    (hN : ∀ i, (N i).IsPositive)
    (hdec : ∀ i, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)).IsPositive)
    (hsmall : ∀ i v, ⟪v, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)) v⟫_ℝ ≤
      (1 / 2 : ℝ) * ⟪v, Q i v⟫_ℝ)
    {epsilon beta G g g₀ K : ℝ}
    (hepsilon : 0 ≤ epsilon) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1)
    (hG : 0 ≤ G) (hg : 1 ≤ g) (hbg : beta * g < 1)
    (hg₀ : 0 ≤ g₀) (hK : 0 ≤ K) (hbg₀ : beta * g₀ < 1)
    (hgrowth : ∀ j i, j ≤ i → ∀ v,
      ⟪v, Q j v⟫_ℝ ≤ G * g ^ (i - j) * ⟪v, Q i v⟫_ℝ)
    (hnorm : ∀ i v, ‖(Q i).symm v‖ ^ 2 ≤ K * g₀ ^ i * ‖v‖ ^ 2)
    (hNsmall : ∀ i v, ⟪v, N i v⟫_ℝ ≤ epsilon * ⟪v, Q i v⟫_ℝ)
    (henvelope : ∀ i v, ⟪v, F i v⟫_ℝ ≤ beta ^ i * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range (i + 1), beta ^ (i - j) * ⟪v, N j v⟫_ℝ)
    (xi : E) (k : ℕ) :
    (∑ i ∈ Finset.range k, ⟪(Q i).symm xi, F i ((Q i).symm xi)⟫_ℝ) ≤
      K * (1 - beta * g₀)⁻¹ * ‖xi‖ ^ 2 +
        2 * (1 - beta)⁻¹ *
          (∑ i ∈ Finset.range k, ⟪(Q i).symm xi, N i ((Q i).symm xi)⟫_ℝ) +
        2 * epsilon * G * geometricIntervalConstant (beta * g) *
          (⟪xi, (Q k).symm xi⟫_ℝ - ⟪xi, (Q 0).symm xi⟫_ℝ) := by
  let a : ℕ → E := fun i => (Q i).symm xi
  let b : ℕ → ℝ := fun i =>
    ⟪xi, (((Q (i + 1)).symm : E →L[ℝ] E) - ((Q i).symm : E →L[ℝ] E)) xi⟫_ℝ
  have hb i : 0 ≤ b i :=
    (inverse_increment_isPositive (Q i) (Q (i + 1)) (hQ i) (hQ (i + 1)) (hdec i)).inner_nonneg_right xi
  have hconv := moving_form_convolution_le (fun i => (Q i : E →L[ℝ] E)) N hN a b hb
    hepsilon hbeta hbeta1 hG (by linarith : 0 ≤ g) hbg hNsmall
    (fun j i hji => inverse_vector_interval_energy Q hQ hdec hsmall hG hg hgrowth xi hji) k
  have hback := inverse_background_sum_le a xi hbeta hg₀ hK hbg₀
    (fun i => hnorm i xi) k
  have henv := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range k) => henvelope i (a i))
  rw [Finset.sum_add_distrib] at henv
  have htotal := henv.trans (add_le_add hback hconv)
  change _ ≤ _ + (_ + 2 * epsilon * G * geometricIntervalConstant (beta * g) *
    ∑ i ∈ Finset.range k, b i) at htotal
  dsimp only [b] at htotal
  rw [inverse_energy_telescopes] at htotal
  simpa only [add_assoc] using htotal

/-- The actual central cumulative comparison and weighted heat total follow
from the two heat decrement inequalities. The smallness condition absorbs the
moving-normalization error; it does not assume a cumulative conclusion. -/
theorem inverse_heat_cumulative_comparison (Q : ℕ → E ≃L[ℝ] E)
    (N F : ℕ → E →L[ℝ] E)
    (hQ : ∀ i, (Q i : E →L[ℝ] E).IsPositive)
    (hN : ∀ i, (N i).IsPositive)
    (hdec : ∀ i, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)).IsPositive)
    (hsmall : ∀ i v, ⟪v, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)) v⟫_ℝ ≤
      (1 / 2 : ℝ) * ⟪v, Q i v⟫_ℝ)
    {epsilon beta G g g₀ K C K₀ : ℝ}
    (hepsilon : 0 ≤ epsilon) (hbeta : 0 ≤ beta) (hbeta1 : beta < 1)
    (hG : 0 ≤ G) (hg : 1 ≤ g) (hbg : beta * g < 1)
    (hg₀ : 0 ≤ g₀) (hK : 0 ≤ K) (hbg₀ : beta * g₀ < 1)
    (hC : 0 ≤ C) (hK₀ : 0 ≤ K₀)
    (hgrowth : ∀ j i, j ≤ i → ∀ v,
      ⟪v, Q j v⟫_ℝ ≤ G * g ^ (i - j) * ⟪v, Q i v⟫_ℝ)
    (hnorm : ∀ i v, ‖(Q i).symm v‖ ^ 2 ≤ K * g₀ ^ i * ‖v‖ ^ 2)
    (hNsmall : ∀ i v, ⟪v, N i v⟫_ℝ ≤ epsilon * ⟪v, Q i v⟫_ℝ)
    (henvelope : ∀ i v, ⟪v, F i v⟫_ℝ ≤ beta ^ i * ‖v‖ ^ 2 +
      ∑ j ∈ Finset.range (i + 1), beta ^ (i - j) * ⟪v, N j v⟫_ℝ)
    (hlower : ∀ i v, ⟪v, N i v⟫_ℝ ≤
      C * ⟪v, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)) v⟫_ℝ)
    (hupper : ∀ i v,
      ⟪v, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)) v⟫_ℝ ≤ C * ⟪v, F i v⟫_ℝ)
    (hbase : ∀ v, ⟪v, (Q 0).symm v⟫_ℝ ≤ K₀ * ‖v‖ ^ 2 ∧
      ‖v‖ ^ 2 ≤ K₀ * ⟪v, (Q 0).symm v⟫_ℝ)
    (habsorb : 2 * C * (2 * G * geometricIntervalConstant (beta * g)) * epsilon ≤ 1 / 2)
    (xi : E) (k : ℕ) :
    let R := K * (1 - beta * g₀)⁻¹
    let P := 2 * (1 - beta)⁻¹
    let W := 2 * G * geometricIntervalConstant (beta * g)
    let H := ⟪xi, (Q k).symm xi⟫_ℝ
    let n := ∑ i ∈ Finset.range k, ⟪(Q i).symm xi, N i ((Q i).symm xi)⟫_ℝ
    (∑ i ∈ Finset.range k, ⟪(Q i).symm xi, F i ((Q i).symm xi)⟫_ℝ) ≤
      (R * K₀ + P * C + W * epsilon) * H ∧
    ‖xi‖ ^ 2 + n ≤ (K₀ + C) * H ∧
    H ≤ 2 * (K₀ + 2 * C * R) * ‖xi‖ ^ 2 + 4 * C * P * n := by
  let R := K * (1 - beta * g₀)⁻¹
  let P := 2 * (1 - beta)⁻¹
  let W := 2 * G * geometricIntervalConstant (beta * g)
  let H := ⟪xi, (Q k).symm xi⟫_ℝ
  let H₀ := ⟪xi, (Q 0).symm xi⟫_ℝ
  let n := ∑ i ∈ Finset.range k, ⟪(Q i).symm xi, N i ((Q i).symm xi)⟫_ℝ
  let f := ∑ i ∈ Finset.range k, ⟪(Q i).symm xi, F i ((Q i).symm xi)⟫_ℝ
  let b : ℕ → ℝ := fun i =>
    ⟪xi, (((Q (i + 1)).symm : E →L[ℝ] E) - ((Q i).symm : E →L[ℝ] E)) xi⟫_ℝ
  have hR : 0 ≤ R := mul_nonneg hK (inv_nonneg.mpr (by linarith))
  have hP : 0 ≤ P := mul_nonneg (by norm_num) (inv_nonneg.mpr (by linarith))
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg (by norm_num) hG)
    (geometricIntervalConstant_nonneg (mul_nonneg hbeta (by linarith)))
  have hH₀ : 0 ≤ H₀ := (positive_equiv_symm (Q 0) (hQ 0)).inner_nonneg_right xi
  have hb (i : ℕ) : 0 ≤ b i :=
    (inverse_increment_isPositive (Q i) (Q (i + 1)) (hQ i) (hQ (i + 1)) (hdec i)).inner_nonneg_right xi
  have htel : (∑ i ∈ Finset.range k, b i) = H - H₀ := inverse_energy_telescopes Q xi k
  have hmono : H₀ ≤ H := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range k) => hb i)
    rw [htel] at hh
    linarith
  have hnormH : ‖xi‖ ^ 2 ≤ K₀ * H := (hbase xi).2.trans
    (mul_le_mul_of_nonneg_left hmono hK₀)
  have hnb (i : ℕ) : ⟪(Q i).symm xi, N i ((Q i).symm xi)⟫_ℝ ≤ C * b i := by
    have ho := (inverse_increment_order (Q i) (Q (i + 1)) (hQ i) (hQ (i + 1))
      (hdec i) (by norm_num) (by norm_num) (hsmall i) xi).1
    exact (hlower i ((Q i).symm xi)).trans (mul_le_mul_of_nonneg_left ho hC)
  have hbf (i : ℕ) : b i ≤ 2 * C * ⟪(Q i).symm xi, F i ((Q i).symm xi)⟫_ℝ := by
    have ho := (inverse_increment_order (Q i) (Q (i + 1)) (hQ i) (hQ (i + 1))
      (hdec i) (by norm_num) (by norm_num) (hsmall i) xi).2
    have ho' := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 2)).mp ho
    have hh := hupper i ((Q i).symm xi)
    change b i * (1 - 1 / 2) ≤
      ⟪(Q i).symm xi, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)) ((Q i).symm xi)⟫_ℝ at ho'
    linarith
  have hnH : n ≤ C * H := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range k) => hnb i)
    rw [← Finset.mul_sum, htel] at hh
    change n ≤ C * (H - H₀) at hh
    nlinarith
  have hHf : H - H₀ ≤ 2 * C * f := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range k) => hbf i)
    rw [← Finset.mul_sum, htel] at hh
    exact hh
  have henv : f ≤ R * ‖xi‖ ^ 2 + P * n + W * epsilon * (H - H₀) := by
    have hh := inverse_heat_envelope_sum_le Q N F hQ hN hdec hsmall hepsilon hbeta
      hbeta1 hG hg hbg hg₀ hK hbg₀ hgrowth hnorm hNsmall henvelope xi k
    convert hh using 1
    dsimp only [R, P, W, H, H₀, n, f]
    ring
  have henv' : f ≤ R * ‖xi‖ ^ 2 + P * n + W * epsilon * H := by
    have hh : W * epsilon * (H - H₀) ≤ W * epsilon * H :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hW hepsilon)
    linarith
  change f ≤ (R * K₀ + P * C + W * epsilon) * H ∧
    ‖xi‖ ^ 2 + n ≤ (K₀ + C) * H ∧
    H ≤ 2 * (K₀ + 2 * C * R) * ‖xi‖ ^ 2 + 4 * C * P * n
  refine ⟨?_, ?_, ?_⟩
  · have h₁ := mul_le_mul_of_nonneg_left hnormH hR
    have h₂ := mul_le_mul_of_nonneg_left hnH hP
    nlinarith
  · linarith
  · have hh := mul_le_mul_of_nonneg_left henv' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
    have hba := (hbase xi).1
    have hH : 0 ≤ H := hH₀.trans hmono
    have ha : 2 * C * (W * epsilon) * H ≤ (1 / 2 : ℝ) * H := by
      apply mul_le_mul_of_nonneg_right _ hH
      simpa only [W, mul_assoc] using habsorb
    nlinarith

/-- The lower heat decrement controls all finite families of enlarged mass
forms, with the cardinal bound as the only dependence on the family. -/
theorem enlarged_mass_inverse_sum_le {ι : Type*}
    (Q : ℕ → E ≃L[ℝ] E) (M : ℕ → ι → E →L[ℝ] E) (s : ℕ → Finset ι)
    (hQ : ∀ i, (Q i : E →L[ℝ] E).IsPositive)
    (hdec : ∀ i, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)).IsPositive)
    (hsmall : ∀ i v, ⟪v, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)) v⟫_ℝ ≤
      (1 / 2 : ℝ) * ⟪v, Q i v⟫_ℝ)
    {C : ℝ} (hC : 0 ≤ C) (J : ℕ) (hcard : ∀ i, (s i).card ≤ J)
    (hmass : ∀ i y, y ∈ s i → ∀ v, ⟪v, M i y v⟫_ℝ ≤
      C * ⟪v, ((Q i : E →L[ℝ] E) - (Q (i + 1) : E →L[ℝ] E)) v⟫_ℝ)
    (xi : E) (k : ℕ) :
    (∑ i ∈ Finset.range k, ∑ y ∈ s i, ⟪(Q i).symm xi, M i y ((Q i).symm xi)⟫_ℝ) ≤
      (J : ℝ) * C * ⟪xi, (Q k).symm xi⟫_ℝ := by
  let b : ℕ → ℝ := fun i =>
    ⟪xi, (((Q (i + 1)).symm : E →L[ℝ] E) - ((Q i).symm : E →L[ℝ] E)) xi⟫_ℝ
  have hb i : 0 ≤ b i :=
    (inverse_increment_isPositive (Q i) (Q (i + 1)) (hQ i) (hQ (i + 1)) (hdec i)).inner_nonneg_right xi
  have hpoint i y (hy : y ∈ s i) :
      ⟪(Q i).symm xi, M i y ((Q i).symm xi)⟫_ℝ ≤ C * b i := by
    have ho := (inverse_increment_order (Q i) (Q (i + 1)) (hQ i) (hQ (i + 1))
      (hdec i) (by norm_num) (by norm_num) (hsmall i) xi).1
    exact (hmass i y hy ((Q i).symm xi)).trans (mul_le_mul_of_nonneg_left ho hC)
  calc
    _ ≤ ∑ i ∈ Finset.range k, (J : ℝ) * (C * b i) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∑ y ∈ s i, C * b i := Finset.sum_le_sum fun y hy => hpoint i y hy
        _ = ((s i).card : ℝ) * (C * b i) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard i) (mul_nonneg hC (hb i))
    _ = (J : ℝ) * C * (⟪xi, (Q k).symm xi⟫_ℝ - ⟪xi, (Q 0).symm xi⟫_ℝ) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      dsimp only [b]
      rw [inverse_energy_telescopes]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sub_le_self _ ((positive_equiv_symm (Q 0) (hQ 0)).inner_nonneg_right xi))
      (mul_nonneg (Nat.cast_nonneg J) hC)

end RegularPointCoordinates

end

end OAI

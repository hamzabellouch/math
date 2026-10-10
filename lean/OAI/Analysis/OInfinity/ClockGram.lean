import OAI.Analysis.OInfinity.ClockCancellation

namespace OAI

/-! # Both Gram errors of the actual clock-corrected path

The homogeneous convolution identities follow from the two-isometry
cancellation formula. The failure of the clock to
commute with its three coefficients is retained quantitatively. Both Gram
errors are controlled; neither invertibility nor unitarity is assumed.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

lemma clock_commutator_star (k : unitary E) (x : E) :
    ‖star x * (k : E) - (k : E) * star x‖ =
      ‖x * (k : E) - (k : E) * x‖ := by
  have hk : star (k : E) = ((k⁻¹ : unitary E) : E) := by
    rw [← Unitary.coe_star, Unitary.star_eq_inv]
  calc
    _ = ‖star (x * star (k : E) - star (k : E) * x)‖ := by
      simp only [star_sub, star_mul, star_star]
      exact norm_sub_rev _ _
    _ = ‖x * star (k : E) - star (k : E) * x‖ := norm_star _
    _ = ‖x * ((k⁻¹ : unitary E) : E) - ((k⁻¹ : unitary E) : E) * x‖ := by rw [hk]
    _ = _ := clock_commutator_inverse k x

lemma clockDegreeCorrection_star_error (k : unitary E) (d : ℤ) (x : E) :
    ‖star (clockDegreeCorrection k d x) - clockDegreeCorrection k (-d) (star x)‖ ≤
      (d.natAbs : ℝ) * ‖x * (k : E) - (k : E) * x‖ := by
  rw [clockDegreeCorrection_star_defect]
  simpa only [clock_commutator_star] using clock_commutator_zpow k (star x) d

lemma clock_three_sum_norm (k : unitary E) (d : Fin 3 → ℤ) (x : Fin 3 → E)
    (M : ℝ) (hx : ∀ i, ‖x i‖ ≤ M) :
    ‖∑ i, clockDegreeCorrection k (d i) (x i)‖ ≤ 3 * M := by
  calc
    _ ≤ ∑ i, ‖clockDegreeCorrection k (d i) (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, M := by
      exact Finset.sum_le_sum fun i _ => (clockDegreeCorrection_norm k (d i) (x i)).le.trans (hx i)
    _ = _ := by simp

lemma clock_three_sum_star_error (k : unitary E) (d : Fin 3 → ℤ) (x : Fin 3 → E)
    (δ : ℝ) (hδ : 0 ≤ δ) (hd : ∀ i, (d i).natAbs ≤ 1)
    (hc : ∀ i, ‖x i * (k : E) - (k : E) * x i‖ ≤ δ) :
    ‖star (∑ i, clockDegreeCorrection k (d i) (x i)) -
      ∑ i, clockDegreeCorrection k (-d i) (star (x i))‖ ≤ 3 * δ := by
  rw [star_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖star (clockDegreeCorrection k (d i) (x i)) -
        clockDegreeCorrection k (-d i) (star (x i))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 3, δ := by
      apply Finset.sum_le_sum
      intro i _
      apply (clockDegreeCorrection_star_error k (d i) (x i)).trans
      calc
        _ ≤ (d i).natAbs * δ := mul_le_mul_of_nonneg_left (hc i) (by positivity)
        _ ≤ δ := mul_le_of_le_one_left hδ (by exact_mod_cast hd i)
    _ = _ := by simp

lemma clock_three_sum_product_error (k : unitary E)
    (d e : Fin 3 → ℤ) (x y : Fin 3 → E) (δ M : ℝ)
    (hδ : 0 ≤ δ) (he : ∀ i, (e i).natAbs ≤ 1)
    (hc : ∀ i, ‖x i * (k : E) - (k : E) * x i‖ ≤ δ)
    (hy : ∀ i, ‖y i‖ ≤ M) :
    ‖(∑ i, clockDegreeCorrection k (d i) (x i)) *
        (∑ j, clockDegreeCorrection k (e j) (y j)) -
      ∑ i, ∑ j, clockDegreeCorrection k (d i + e j) (x i * y j)‖ ≤ 9 * δ * M := by
  apply (clockDegreeCorrection_sum_product_error k d e x y).trans
  calc
    _ ≤ ∑ _ : Fin 3, ∑ _ : Fin 3, δ * M := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hp : ‖x i * ((k ^ (-e j) : unitary E) : E) -
          ((k ^ (-e j) : unitary E) : E) * x i‖ ≤ δ := by
        apply (clock_commutator_zpow k (x i) (-e j)).trans
        rw [Int.natAbs_neg]
        calc
          _ ≤ (e j).natAbs * δ := mul_le_mul_of_nonneg_left (hc i) (by positivity)
          _ ≤ δ := mul_le_of_le_one_left hδ (by exact_mod_cast he j)
      exact mul_le_mul hp (hy j) (norm_nonneg _) hδ
    _ = _ := by simp; ring

/-- Exact convolution and small coefficient commutators bound the initial
Gram error. The cardinality here is exactly the three terms used above. -/
lemma clock_three_initial_gram_error (k : unitary E)
    (d : Fin 3 → ℤ) (x : Fin 3 → E) (δ M : ℝ)
    (hδ : 0 ≤ δ) (_hM : 0 ≤ M) (hd : ∀ i, (d i).natAbs ≤ 1)
    (hc : ∀ i, ‖x i * (k : E) - (k : E) * x i‖ ≤ δ)
    (hx : ∀ i, ‖x i‖ ≤ M)
    (hg : (∑ i, ∑ j, clockDegreeCorrection k (-d i + d j) (star (x i) * x j)) = 1) :
    ‖star (∑ i, clockDegreeCorrection k (d i) (x i)) *
      (∑ i, clockDegreeCorrection k (d i) (x i)) - 1‖ ≤ 18 * M * δ := by
  let z := ∑ i, clockDegreeCorrection k (d i) (x i)
  let y := ∑ i, clockDegreeCorrection k (-d i) (star (x i))
  have hz : ‖z‖ ≤ 3 * M := clock_three_sum_norm k d x M hx
  have hstar : ‖star z - y‖ ≤ 3 * δ := clock_three_sum_star_error k d x δ hδ hd hc
  have hyz : ‖y * z - 1‖ ≤ 9 * δ * M := by
    have hp := clock_three_sum_product_error k (fun i => -d i) d
      (fun i => star (x i)) x δ M hδ hd
      (fun i => (clock_commutator_star k (x i)).le.trans (hc i)) hx
    simpa only [hg] using hp
  change ‖star z * z - 1‖ ≤ _
  calc
    _ ≤ ‖star z * z - y * z‖ + ‖y * z - 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖(star z - y) * z‖ + ‖y * z - 1‖ := by rw [sub_mul]
    _ ≤ ‖star z - y‖ * ‖z‖ + ‖y * z - 1‖ := add_le_add (norm_mul_le _ _) le_rfl
    _ ≤ (3 * δ) * (3 * M) + 9 * δ * M :=
      add_le_add (mul_le_mul hstar hz (norm_nonneg _) (by positivity)) hyz
    _ = _ := by ring

/-- The same argument controls the final Gram error independently. -/
lemma clock_three_final_gram_error (k : unitary E)
    (d : Fin 3 → ℤ) (x : Fin 3 → E) (δ M : ℝ)
    (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hd : ∀ i, (d i).natAbs ≤ 1)
    (hc : ∀ i, ‖x i * (k : E) - (k : E) * x i‖ ≤ δ)
    (hx : ∀ i, ‖x i‖ ≤ M)
    (hg : (∑ i, ∑ j, clockDegreeCorrection k (d i - d j) (x i * star (x j))) = 1) :
    ‖(∑ i, clockDegreeCorrection k (d i) (x i)) *
      star (∑ i, clockDegreeCorrection k (d i) (x i)) - 1‖ ≤ 18 * M * δ := by
  let z := ∑ i, clockDegreeCorrection k (d i) (x i)
  let y := ∑ i, clockDegreeCorrection k (-d i) (star (x i))
  have hz : ‖z‖ ≤ 3 * M := clock_three_sum_norm k d x M hx
  have hstar : ‖star z - y‖ ≤ 3 * δ := clock_three_sum_star_error k d x δ hδ hd hc
  have hzy : ‖z * y - 1‖ ≤ 9 * δ * M := by
    have hp := clock_three_sum_product_error k d (fun i => -d i)
      x (fun i => star (x i)) δ M hδ (fun i => by simpa only [Int.natAbs_neg] using hd i)
      hc (fun i => (norm_star (x i)).le.trans (hx i))
    simp only [← sub_eq_add_neg, hg] at hp
    exact hp
  change ‖z * star z - 1‖ ≤ _
  calc
    _ ≤ ‖z * star z - z * y‖ + ‖z * y - 1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖z * (star z - y)‖ + ‖z * y - 1‖ := by rw [mul_sub]
    _ ≤ ‖z‖ * ‖star z - y‖ + ‖z * y - 1‖ := add_le_add (norm_mul_le _ _) le_rfl
    _ ≤ (3 * M) * (3 * δ) + 9 * δ * M :=
      add_le_add (mul_le_mul hz hstar (norm_nonneg _) (by positivity)) hzy
    _ = _ := by ring

/-- Both Gram errors for the actual corrected cancellation, with precisely
the coefficient commutators still to be supplied by the chosen finite clock. -/
lemma clockCorrectedCancellation_gram_errors (k : unitary E) (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hu : u ∈ unitary E) (θ δ M : ℝ) (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hc : ∀ i, ‖clockCancellationCoefficients a b u θ i * (k : E) -
      (k : E) * clockCancellationCoefficients a b u θ i‖ ≤ δ)
    (hx : ∀ i, ‖clockCancellationCoefficients a b u θ i‖ ≤ M) :
    ‖star (clockCorrectedCancellation k a b u θ) *
        clockCorrectedCancellation k a b u θ - 1‖ ≤ 18 * M * δ ∧
    ‖clockCorrectedCancellation k a b u θ *
        star (clockCorrectedCancellation k a b u θ) - 1‖ ≤ 18 * M * δ := by
  have hd (i : Fin 3) : (clockCancellationDegrees i).natAbs ≤ 1 := by
    fin_cases i <;> norm_num [clockCancellationDegrees]
  have hg := clockCancellation_convolution_grams k a b u ha hb hab hu θ
  simp only [clockCorrectedCancellation_eq_sum]
  exact ⟨clock_three_initial_gram_error k _ _ δ M hδ hM hd hc hx hg.1,
    clock_three_final_gram_error k _ _ δ M hδ hM hd hc hx hg.2⟩


private lemma clock_isometry_norm (x : E) (hx : star x * x = 1) : ‖x‖ ≤ 1 := by
  have h := congrArg norm hx
  rw [CStarRing.norm_star_mul_self] at h
  have h1 : ‖(1 : E)‖ ≤ 1 := (IsStarProjection.one E).norm_le
  nlinarith [norm_nonneg x]

private lemma clock_triple_norm (a x b : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a * x * star b‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖a * x‖ * ‖star b‖ := norm_mul_le _ _
    _ ≤ (‖a‖ * ‖x‖) * ‖b‖ := by rw [norm_star]; gcongr; exact norm_mul_le _ _
    _ ≤ (1 * ‖x‖) * 1 := by gcongr
    _ = _ := by ring

/-- All three actual coefficients have a uniform norm bound in the path
parameter. -/
lemma clockCancellationCoefficients_norm_le (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1)
    (hu : u ∈ unitary E) (θ : ℝ) (i : Fin 3) :
    ‖clockCancellationCoefficients a b u θ i‖ ≤ 5 := by
  have han := clock_isometry_norm a ha
  have hbn := clock_isometry_norm b hb
  have hun := clock_isometry_norm u hu.1
  have hum : ‖u - 1‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by linarith [(IsStarProjection.one E).norm_le])
  have hus : ‖star u - 1‖ ≤ 2 := by
    calc
      _ = ‖star (u - 1)‖ := by rw [star_sub, star_one]
      _ = ‖u - 1‖ := norm_star _
      _ ≤ 2 := hum
  have hX : ‖clockCancellationCross a b u‖ ≤ 2 := (clock_triple_norm a _ b han hbn).trans hum
  have hC : ‖clockCancellationIncrement a b u‖ ≤ 4 := by
    apply (norm_add_le _ _).trans
    have h₁ := (clock_triple_norm a _ a han han).trans hum
    have h₂ := (clock_triple_norm b _ b hbn hbn).trans hus
    linarith
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hsin : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hν : |Real.sin θ * Real.cos θ| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hsin hcos (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hτ : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_pow]
    nlinarith [mul_self_le_mul_self (abs_nonneg (Real.cos θ)) hcos]
  fin_cases i
  · change ‖1 + (Real.cos θ ^ 2) • clockCancellationIncrement a b u‖ ≤ 5
    calc
      _ ≤ ‖(1 : E)‖ + ‖(Real.cos θ ^ 2) • clockCancellationIncrement a b u‖ := norm_add_le _ _
      _ ≤ 1 + 1 * 4 := by rw [norm_smul, Real.norm_eq_abs]; gcongr; exact (IsStarProjection.one E).norm_le
      _ = _ := by norm_num
  · change ‖(Real.sin θ * Real.cos θ) • clockCancellationCross a b u‖ ≤ 5
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |Real.sin θ * Real.cos θ| * ‖clockCancellationCross a b u‖ ≤ 1 * 2 := by gcongr
      _ ≤ 5 := by norm_num
  · change ‖-(Real.sin θ * Real.cos θ) • star (clockCancellationCross a b u)‖ ≤ 5
    rw [norm_smul, Real.norm_eq_abs, abs_neg, norm_star]
    calc
      |Real.sin θ * Real.cos θ| * ‖clockCancellationCross a b u‖ ≤ 1 * 2 := by gcongr
      _ ≤ 5 := by norm_num

private lemma clock_product_commutator (k : unitary E) (x y : E) :
    ‖x * y * (k : E) - (k : E) * (x * y)‖ ≤
      ‖x‖ * ‖y * (k : E) - (k : E) * y‖ +
        ‖x * (k : E) - (k : E) * x‖ * ‖y‖ := by
  have he : x * y * (k : E) - (k : E) * (x * y) =
      x * (y * (k : E) - (k : E) * y) + (x * (k : E) - (k : E) * x) * y := by
    noncomm_ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

private lemma clock_triple_commutator (k : unitary E) (a x b : E) (δ : ℝ)
    (hδ : 0 ≤ δ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hx : ‖x‖ ≤ 2)
    (hca : ‖a * (k : E) - (k : E) * a‖ ≤ δ)
    (hcb : ‖b * (k : E) - (k : E) * b‖ ≤ δ)
    (hcx : ‖x * (k : E) - (k : E) * x‖ ≤ δ) :
    ‖(a * x * star b) * (k : E) - (k : E) * (a * x * star b)‖ ≤ 5 * δ := by
  have hn : ‖a * x‖ ≤ 2 := by
    calc
      _ ≤ ‖a‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ 1 * 2 := by gcongr
      _ = 2 := by norm_num
  have hax : ‖a * x * (k : E) - (k : E) * (a * x)‖ ≤ 3 * δ := by
    apply (clock_product_commutator k a x).trans
    calc
      _ ≤ 1 * δ + δ * 2 := by gcongr
      _ = _ := by ring
  apply (clock_product_commutator k (a * x) (star b)).trans
  rw [norm_star, clock_commutator_star]
  calc
    _ ≤ 2 * δ + (3 * δ) * 1 := by gcongr
    _ = _ := by ring

/-- The actual coefficients commute with the clock whenever the two supplied
isometries and the supplied unitary do; the bound is uniform in the angle. -/
lemma clockCancellationCoefficients_commutator_le (k : unitary E) (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hu : u ∈ unitary E)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hca : ‖a * (k : E) - (k : E) * a‖ ≤ δ)
    (hcb : ‖b * (k : E) - (k : E) * b‖ ≤ δ)
    (hcu : ‖u * (k : E) - (k : E) * u‖ ≤ δ) (θ : ℝ) (i : Fin 3) :
    ‖clockCancellationCoefficients a b u θ i * (k : E) -
      (k : E) * clockCancellationCoefficients a b u θ i‖ ≤ 10 * δ := by
  have han := clock_isometry_norm a ha
  have hbn := clock_isometry_norm b hb
  have hun := clock_isometry_norm u hu.1
  have hum : ‖u - 1‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [(IsStarProjection.one E).norm_le])
  have hus : ‖star u - 1‖ ≤ 2 := by
    calc
      _ = ‖star (u - 1)‖ := by rw [star_sub, star_one]
      _ = ‖u - 1‖ := norm_star _
      _ ≤ 2 := hum
  have huc : ‖(u - 1) * (k : E) - (k : E) * (u - 1)‖ ≤ δ := by
    convert hcu using 1; congr 1; noncomm_ring
  have husc : ‖(star u - 1) * (k : E) - (k : E) * (star u - 1)‖ ≤ δ := by
    have h := (clock_commutator_star k u).le.trans hcu
    convert h using 1; congr 1; noncomm_ring
  have hA := clock_triple_commutator k a (u - 1) a δ hδ han han hum hca hca huc
  have hB := clock_triple_commutator k b (star u - 1) b δ hδ hbn hbn hus hcb hcb husc
  have hX := clock_triple_commutator k a (u - 1) b δ hδ han hbn hum hca hcb huc
  have hC : ‖clockCancellationIncrement a b u * (k : E) -
      (k : E) * clockCancellationIncrement a b u‖ ≤ 10 * δ := by
    unfold clockCancellationIncrement
    have he : (a * (u - 1) * star a + b * (star u - 1) * star b) * (k : E) -
        (k : E) * (a * (u - 1) * star a + b * (star u - 1) * star b) =
        (a * (u - 1) * star a * (k : E) - (k : E) * (a * (u - 1) * star a)) +
        (b * (star u - 1) * star b * (k : E) - (k : E) * (b * (star u - 1) * star b)) := by
      noncomm_ring
    rw [he]
    exact (norm_add_le _ _).trans (by linarith)
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hsin : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hν : |Real.sin θ * Real.cos θ| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hsin hcos (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hτ : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_pow]
    nlinarith [mul_self_le_mul_self (abs_nonneg (Real.cos θ)) hcos]
  have hr (r : ℝ) (x : E) :
      ‖(r • x) * (k : E) - (k : E) * (r • x)‖ = |r| * ‖x * (k : E) - (k : E) * x‖ := by
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, norm_smul, Real.norm_eq_abs]
  fin_cases i
  · change ‖(1 + (Real.cos θ ^ 2) • clockCancellationIncrement a b u) * (k : E) -
        (k : E) * (1 + (Real.cos θ ^ 2) • clockCancellationIncrement a b u)‖ ≤ _
    have he (r : ℝ) (x : E) : (1 + r • x) * (k : E) - (k : E) * (1 + r • x) =
        (r • x) * (k : E) - (k : E) * (r • x) := by noncomm_ring
    rw [he, hr]
    exact (mul_le_mul hτ hC (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · change ‖((Real.sin θ * Real.cos θ) • clockCancellationCross a b u) * (k : E) -
        (k : E) * ((Real.sin θ * Real.cos θ) • clockCancellationCross a b u)‖ ≤ _
    rw [hr]
    have hx : ‖clockCancellationCross a b u * (k : E) - (k : E) * clockCancellationCross a b u‖ ≤ 5 * δ := hX
    exact (mul_le_mul hν hx (norm_nonneg _) (by norm_num)).trans (by nlinarith)
  · change ‖(-(Real.sin θ * Real.cos θ) • star (clockCancellationCross a b u)) * (k : E) -
        (k : E) * (-(Real.sin θ * Real.cos θ) • star (clockCancellationCross a b u))‖ ≤ _
    rw [hr, abs_neg, clock_commutator_star]
    have hx : ‖clockCancellationCross a b u * (k : E) - (k : E) * clockCancellationCross a b u‖ ≤ 5 * δ := hX
    exact (mul_le_mul hν hx (norm_nonneg _) (by norm_num)).trans (by nlinarith)

/-- Uniform quantitative near-unitarity of the actual corrected path, from
only its constituent commutators. -/
lemma clockCorrectedCancellation_gram_errors_of_constituents (k : unitary E) (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1) (hab : star a * b = 0)
    (hu : u ∈ unitary E) (δ : ℝ) (hδ : 0 ≤ δ)
    (hca : ‖a * (k : E) - (k : E) * a‖ ≤ δ)
    (hcb : ‖b * (k : E) - (k : E) * b‖ ≤ δ)
    (hcu : ‖u * (k : E) - (k : E) * u‖ ≤ δ) (θ : ℝ) :
    ‖star (clockCorrectedCancellation k a b u θ) *
        clockCorrectedCancellation k a b u θ - 1‖ ≤ 900 * δ ∧
    ‖clockCorrectedCancellation k a b u θ *
        star (clockCorrectedCancellation k a b u θ) - 1‖ ≤ 900 * δ := by
  have h := clockCorrectedCancellation_gram_errors k a b u ha hb hab hu θ (10 * δ) 5
    (by positivity) (by norm_num)
    (clockCancellationCoefficients_commutator_le k a b u ha hb hu δ hδ hca hcb hcu θ)
    (clockCancellationCoefficients_norm_le a b u ha hb hu θ)
  simpa only [show 18 * (5 : ℝ) * (10 * δ) = 900 * δ by ring] using h

end WeakPureInfiniteness

end

end OAI

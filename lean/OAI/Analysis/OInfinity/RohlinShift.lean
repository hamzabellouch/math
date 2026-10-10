import OAI.Analysis.OInfinity.JordanWignerEstimates

namespace OAI

/-! # Quantitative cyclic partitions for the finite even-row shift

The exact dyadic projection partition is approximately cycled by the actual
row endomorphism, with an explicit error tending to zero as the geometric
blocks lengthen. No centrality for additional elements or cocycle unitary is
asserted here.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E] {n : ℕ}

lemma carSpinProjection_sub_norm_le (q a b : E) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖carSpinProjection q a ζ - carSpinProjection q b ζ‖ ≤ ‖a - b‖ := by
  have he : carSpinProjection q a ζ - carSpinProjection q b ζ =
      (2 : ℂ)⁻¹ • (ζ • (a - b) + star ζ • star (a - b)) := by
    simp only [carSpinProjection, carSpinAxis, smul_sub, smul_add, star_sub]
    abel
  rw [he, norm_smul]
  have hhalf : ‖(2 : ℂ)⁻¹‖ = (1 / 2 : ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1 / 2 : ℝ) * (‖ζ • (a - b)‖ + ‖star ζ • star (a - b)‖) := by
      gcongr
      exact norm_add_le _ _
    _ = ‖a - b‖ := by rw [norm_smul, norm_smul, norm_star, norm_star, hζ]; ring

lemma carSpinProjection_smul (q a : E) (μ ζ : ℂ) :
    carSpinProjection q (μ • a) ζ = carSpinProjection q a (ζ * μ) := by
  simp only [carSpinProjection, carSpinAxis, star_smul, smul_smul, star_mul]
  rw [mul_comm (star μ) (star ζ)]

lemma evenRowShift_carSpinProjection (q : E) (r : Fin 2 × Fin n → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q) (a : E) (ζ : ℂ) :
    evenRowShift r (carSpinProjection q a ζ) = carSpinProjection q (evenRowShift r a) ζ := by
  simp only [carSpinProjection, carSpinAxis, evenRowShift_smul, evenRowShift_add,
    evenRowShift_unit q r hqstar hqq hrow hsum, ← evenRowShift_star]

lemma evenRowShift_isStarProjection (q : E) (r : Fin 2 × Fin n → E)
    (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (p : E) (hp : IsStarProjection p) (hqp : q * p = p) :
    IsStarProjection (evenRowShift r p) := by
  refine ⟨?_, ?_⟩
  · change evenRowShift r p * evenRowShift r p = evenRowShift r p
    rw [evenRowShift_mul q r hrow p p hqp, hp.isIdempotentElem.eq]
  · change star (evenRowShift r p) = evenRowShift r p
    rw [evenRowShift_star, hp.isSelfAdjoint.star_eq]

variable (q : E) (r : Fin 2 × Fin n → E)
  (hqstar : star q = q) (hqq : q * q = q)
  (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
  (hsum : (∑ i, r i * star (r i)) = q)

include hqstar hqq hrow hsum in
lemma evenRohlin_factor_shift_error (L : ℕ) (hL : 0 < L) (i k : ℕ) :
    ‖evenRowShift r (carSpinProjection q (evenRohlinCoordinate q r L i) (carDyadicPhase i ^ k)) -
      carSpinProjection q (evenRohlinCoordinate q r L i) (carDyadicPhase i ^ (k + 1))‖ ≤
        (4 * (i : ℝ) + 1) * Real.sqrt (18 / (L : ℝ)) := by
  rw [evenRowShift_carSpinProjection q r hqstar hqq hrow hsum, pow_succ,
    ← carSpinProjection_smul]
  exact (carSpinProjection_sub_norm_le q _ _ _
    (by rw [norm_pow, carDyadicPhase_norm, one_pow])).trans
      (evenRohlinCoordinate_shift_error q r hqstar hqq hrow hsum L hL i)

include hqstar hqq hrow hsum in
lemma evenRohlin_factor_properties (L : ℕ) (hL : 0 < L) (i k : ℕ) :
    IsStarProjection (carSpinProjection q (evenRohlinCoordinate q r L i) (carDyadicPhase i ^ k)) ∧
      q * carSpinProjection q (evenRohlinCoordinate q r L i) (carDyadicPhase i ^ k) =
        carSpinProjection q (evenRohlinCoordinate q r L i) (carDyadicPhase i ^ k) := by
  obtain ⟨hl, hr, hz, hg, _, _⟩ := evenRohlinCoordinate_properties q r hqstar hqq hrow hsum L hL
  exact ⟨carSpinProjection_isStarProjection q _ hqstar hqq (hl i) (hr i) (hz i) (hg i) _
    (by rw [norm_pow, carDyadicPhase_norm, one_pow]),
    (carSpinProjection_support q _ hqstar hqq (hl i) (hr i) _).1⟩

include hqstar hqq hrow hsum in
lemma evenRohlinProjection_shift_error (L : ℕ) (hL : 0 < L) (m k : ℕ) :
    ‖evenRowShift r (evenRohlinProjection q r L m k) -
      evenRohlinProjection q r L m (k + 1)‖ ≤
        (m : ℝ) * (4 * (m : ℝ) + 1) * Real.sqrt (18 / (L : ℝ)) := by
  induction m with
  | zero =>
    change ‖evenRowShift r q - q‖ ≤ _
    rw [evenRowShift_unit q r hqstar hqq hrow hsum, sub_self, norm_zero]
    simp
  | succ m ih =>
    let P := evenRohlinProjection q r L m k
    let P' := evenRohlinProjection q r L m (k + 1)
    let e := carSpinProjection q (evenRohlinCoordinate q r L m) (carDyadicPhase m ^ k)
    let e' := carSpinProjection q (evenRohlinCoordinate q r L m) (carDyadicPhase m ^ (k + 1))
    let δ := Real.sqrt (18 / (L : ℝ))
    have heprops := evenRohlin_factor_properties q r hqstar hqq hrow hsum L hL m k
    have henorm : ‖evenRowShift r e‖ ≤ 1 := IsStarProjection.norm_le _
      (evenRowShift_isStarProjection q r hrow e heprops.1 heprops.2)
    have hPnorm : ‖P'‖ ≤ 1 := IsStarProjection.norm_le _
      ((evenRohlinProjection_partition q r hqstar hqq hrow hsum L hL m).1 (k + 1))
    have herr : ‖evenRowShift r e - e'‖ ≤ (4 * (m : ℝ) + 1) * δ :=
      evenRohlin_factor_shift_error q r hqstar hqq hrow hsum L hL m k
    have hdecomp : evenRowShift r (evenRohlinProjection q r L (m + 1) k) -
        evenRohlinProjection q r L (m + 1) (k + 1) =
          (evenRowShift r P - P') * evenRowShift r e + P' * (evenRowShift r e - e') := by
      change evenRowShift r (P * e) - P' * e' = _
      rw [← evenRowShift_mul q r hrow P e heprops.2]
      noncomm_ring
    rw [hdecomp]
    calc
      _ ≤ ‖(evenRowShift r P - P') * evenRowShift r e‖ +
          ‖P' * (evenRowShift r e - e')‖ := norm_add_le _ _
      _ ≤ ‖evenRowShift r P - P'‖ * ‖evenRowShift r e‖ + ‖P'‖ * ‖evenRowShift r e - e'‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ((m : ℝ) * (4 * (m : ℝ) + 1) * δ) * 1 + 1 * ((4 * (m : ℝ) + 1) * δ) := by
        gcongr
      _ ≤ (↑(m + 1) : ℝ) * (4 * (↑(m + 1) : ℝ) + 1) * δ := by
        push_cast
        nlinarith [Real.sqrt_nonneg (18 / (L : ℝ))]

lemma evenRohlinProjection_period (L : ℕ) (m k : ℕ) :
    evenRohlinProjection q r L m (k + 2 ^ m) = evenRohlinProjection q r L m k :=
  dyadicSpinProjection_period q _ carDyadicPhase carDyadicPhase_half m k

include hqstar hqq hrow hsum in
lemma evenRohlinProjection_cyclic_error (L : ℕ) (hL : 0 < L) (m k : ℕ) (hk : k < 2 ^ m) :
    ‖evenRowShift r (evenRohlinProjection q r L m k) -
      evenRohlinProjection q r L m ((k + 1) % (2 ^ m))‖ ≤
        (m : ℝ) * (4 * (m : ℝ) + 1) * Real.sqrt (18 / (L : ℝ)) := by
  have he : evenRohlinProjection q r L m ((k + 1) % (2 ^ m)) =
      evenRohlinProjection q r L m (k + 1) := by
    by_cases hlt : k + 1 < 2 ^ m
    · rw [Nat.mod_eq_of_lt hlt]
    · have heq : k + 1 = 2 ^ m := by omega
      rw [heq, Nat.mod_self]
      simpa only [zero_add] using (evenRohlinProjection_period q r L m 0).symm
  rw [he]
  exact evenRohlinProjection_shift_error q r hqstar hqq hrow hsum L hL m k

include hqstar hqq hrow hsum in
lemma exists_evenRohlin_cyclic_partition (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧
      (∀ k, IsStarProjection (evenRohlinProjection q r L m k)) ∧
      (∑ k ∈ Finset.range (2 ^ m), evenRohlinProjection q r L m k) = q ∧
      (∀ k l, k < 2 ^ m → l < 2 ^ m → k ≠ l →
        evenRohlinProjection q r L m k * evenRohlinProjection q r L m l = 0) ∧
      (∀ k, k < 2 ^ m → ‖evenRowShift r (evenRohlinProjection q r L m k) -
        evenRohlinProjection q r L m ((k + 1) % (2 ^ m))‖ < ε) := by
  let C : ℝ := (m : ℝ) * (4 * (m : ℝ) + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨L, hL⟩ := exists_nat_gt (18 * C ^ 2 / ε ^ 2 + 1)
  have hLpos : 0 < L := by
    have hnonneg : 0 ≤ 18 * C ^ 2 / ε ^ 2 := by positivity
    exact_mod_cast (show (0 : ℝ) < (L : ℝ) by linarith)
  have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hbound : 18 * C ^ 2 < (L : ℝ) * ε ^ 2 := by
    apply (div_lt_iff₀ hεsq).mp
    linarith
  have hbound' : 18 * C ^ 2 / (L : ℝ) < ε ^ 2 := (div_lt_iff₀ hLreal).mpr (by nlinarith)
  have hsqrt := Real.sq_sqrt (show 0 ≤ 18 / (L : ℝ) by positivity)
  have hnorm : C * Real.sqrt (18 / (L : ℝ)) < ε := by
    have he : (C * Real.sqrt (18 / (L : ℝ))) ^ 2 = 18 * C ^ 2 / (L : ℝ) := by
      rw [mul_pow, hsqrt]
      ring
    nlinarith [mul_nonneg hC (Real.sqrt_nonneg (18 / (L : ℝ)))]
  obtain ⟨hp, hsum', horth⟩ := evenRohlinProjection_partition q r hqstar hqq hrow hsum L hLpos m
  refine ⟨L, hLpos, hp, hsum', horth, ?_⟩
  intro k hk
  exact (evenRohlinProjection_cyclic_error q r hqstar hqq hrow hsum L hLpos m k hk).trans_lt hnorm

end WeakPureInfiniteness

end

end OAI

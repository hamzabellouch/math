import OAI.Analysis.OInfinity.MaskedRotations

namespace OAI

/-! # Shifting the actual masked bands

Shifting an iterated-word band changes the input mask from cell zero to
cell one. Reindexing exposes both exceptional cells explicitly, including
the genuine N-th iterate on the cyclic return. No terminal norm estimate
is inferred from its support.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- The shifted finite sum before reindexing its cyclic variable. -/
def shiftedMaskedBand {N : ℕ} [NeZero N] (s : Fin 2 → E)
    (e : ZMod N → E) (d : ZMod N) (x : E) : E :=
  ∑ j, if j = 0 then 0 else
    e (j + d + 1) * finiteRowShiftIterate s (j.val + 1) x * e (j + 1)

private lemma maskedShift_triple_bound (a b c a' c' : E) (η M : ℝ)
    (hη : 0 ≤ η) (hM : 0 ≤ M)
    (ha : ‖a - a'‖ ≤ η) (hc : ‖c - c'‖ ≤ η)
    (ha' : ‖a'‖ ≤ 1) (hc' : ‖c‖ ≤ 1) (hb : ‖b‖ ≤ M) :
    ‖a * b * c - a' * b * c'‖ ≤ 2 * η * M := by
  have he : a * b * c - a' * b * c' =
      (a - a') * b * c + a' * b * (c - c') := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(a - a') * b * c‖ + ‖a' * b * (c - c')‖ := norm_add_le _ _
    _ ≤ (‖a - a'‖ * ‖b‖) * ‖c‖ + (‖a'‖ * ‖b‖) * ‖c - c'‖ := by
      exact add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
    _ ≤ (η * M) * 1 + (1 * M) * η := by gcongr
    _ = _ := by ring

/-- The quantitative shift error comes solely from the supplied cyclic
projection errors; the word iterate itself shifts exactly. -/
lemma maskedBand_shift_approx {N : ℕ} [NeZero N] (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (he : ∀ j, IsStarProjection (e j))
    (d : ZMod N) (x : E) (η : ℝ) (hη : 0 ≤ η)
    (hshift : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η) :
    ‖finiteRowShift s (maskedTowerBand e (Equiv.addRight d)
        (fun j => finiteRowShiftIterate s j.val x) 0) - shiftedMaskedBand s e d x‖ ≤
      2 * (N : ℝ) * η * ‖x‖ := by
  let φ := finiteCuntzDiagonalHom s hs
  have hformula : finiteRowShift s (maskedTowerBand e (Equiv.addRight d)
      (fun j => finiteRowShiftIterate s j.val x) 0) =
      ∑ j : ZMod N, if j = 0 then 0 else
        finiteRowShift s (e (j + d)) * finiteRowShiftIterate s (j.val + 1) x *
          finiteRowShift s (e j) := by
    change φ (∑ j, e (j + d) * maskedBandCoefficients
      (fun j => finiteRowShiftIterate s j.val x) 0 j * e j) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = 0
    · simp only [maskedBandCoefficients, ite_eq_left hj, mul_zero, zero_mul, map_zero]
    · simp only [maskedBandCoefficients, ite_eq_right hj, map_mul]
      rfl
  rw [hformula, shiftedMaskedBand, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ _j : ZMod N, (2 * η * ‖x‖) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = 0
      · simp only [ite_eq_left hj, sub_self, norm_zero]
        positivity
      · simp only [ite_eq_right hj]
        exact maskedShift_triple_bound _ _ _ _ _ η ‖x‖ hη (norm_nonneg x)
          (hshift (j + d)) (hshift j) (he (j + d + 1)).norm_le
          ((finiteCuntzTransfer_norm_le s s hs hs (e j)).trans (he j).norm_le)
          (binaryRowIterate_norm_le s hs (j.val + 1) x)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring

private lemma maskedShift_val_predecessor {N : ℕ} [NeZero N]
    (hN : 1 < N) (k : ZMod N) (hk : k ≠ 0) : (k - 1).val + 1 = k.val := by
  have : Fact (1 < N) := ⟨hN⟩
  have hpos : 1 ≤ k.val := Nat.succ_le_of_lt (ZMod.val_pos.mpr hk)
  rw [ZMod.val_sub (a := k) (b := 1) (by simpa only [ZMod.val_one] using hpos),
    ZMod.val_one]
  omega

private lemma maskedShift_val_return {N : ℕ} [NeZero N] :
    ((-1 : ZMod N).val + 1) = N := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rw [ZMod.val_neg_one]

/-- Reindexing exposes the missing cell one and the returned cell zero.
The coefficient on cell zero is the actual N-th iterate. -/
lemma shiftedMaskedBand_boundary {N : ℕ} [NeZero N] (hN : 1 < N)
    (s : Fin 2 → E) (e : ZMod N → E) (d : ZMod N) (x : E) :
    shiftedMaskedBand s e d x =
      maskedTowerBand e (Equiv.addRight d) (fun j => finiteRowShiftIterate s j.val x) 0 +
        e d * finiteRowShiftIterate s N x * e 0 -
        e (1 + d) * finiteRowShiftIterate s 1 x * e 1 := by
  have : Fact (1 < N) := ⟨hN⟩
  have h10 : (1 : ZMod N) ≠ 0 := one_ne_zero
  have hreindex : shiftedMaskedBand s e d x =
      ∑ k : ZMod N, if k - 1 = 0 then 0 else
        e (k + d) * finiteRowShiftIterate s ((k - 1).val + 1) x * e k := by
    unfold shiftedMaskedBand
    apply Fintype.sum_equiv (Equiv.addRight (1 : ZMod N))
    intro j
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    have hind : j + d + 1 = j + 1 + d := by ring
    rw [hind]
  rw [hreindex]
  have hterm (k : ZMod N) :
      (if k - 1 = 0 then (0 : E) else
        e (k + d) * finiteRowShiftIterate s ((k - 1).val + 1) x * e k) =
      e (k + d) * maskedBandCoefficients (fun j => finiteRowShiftIterate s j.val x) 0 k * e k +
        (if k = 0 then e d * finiteRowShiftIterate s N x * e 0 else 0) -
        (if k = 1 then e (1 + d) * finiteRowShiftIterate s 1 x * e 1 else 0) := by
    by_cases hk0 : k = 0
    · subst k
      have hneg : (-1 : ZMod N) ≠ 0 := neg_ne_zero.mpr h10
      simp only [zero_sub, hneg, ite_false, zero_add, maskedShift_val_return,
        maskedBandCoefficients, ite_true, mul_zero, zero_mul,
        Ne.symm h10, sub_zero, zero_add]
    by_cases hk1 : k = 1
    · subst k
      simp only [sub_self, ite_true, maskedBandCoefficients, ite_eq_right h10,
        ZMod.val_one, add_zero]
    · have hpred : k - 1 ≠ 0 := sub_ne_zero.mpr hk1
      simp only [ite_eq_right hpred, maskedBandCoefficients, ite_eq_right hk0,
        ite_eq_right hk1, maskedShift_val_predecessor hN k hk0, add_zero, sub_zero]
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

/-- The complete generator-shift estimate retains both boundary operators. -/
lemma maskedBand_shift_boundary_error {N : ℕ} [NeZero N] (hN : 1 < N)
    (s : Fin 2 → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (he : ∀ j, IsStarProjection (e j))
    (d : ZMod N) (x : E) (η : ℝ) (hη : 0 ≤ η)
    (hshift : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η) :
    ‖finiteRowShift s (maskedTowerBand e (Equiv.addRight d)
        (fun j => finiteRowShiftIterate s j.val x) 0) -
      (maskedTowerBand e (Equiv.addRight d) (fun j => finiteRowShiftIterate s j.val x) 0 +
        e d * finiteRowShiftIterate s N x * e 0 -
        e (1 + d) * finiteRowShiftIterate s 1 x * e 1)‖ ≤ 2 * (N : ℝ) * η * ‖x‖ := by
  rw [← shiftedMaskedBand_boundary hN]
  exact maskedBand_shift_approx s hs e he d x η hη hshift

/-- Multiplication by an angular coefficient controls the two actual
boundary pieces through its cell-zero and cell-one components. -/
lemma maskedBand_shift_times_bound {N : ℕ} [NeZero N] (hN : 1 < N)
    (s : Fin 2 → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (he : ∀ j, IsStarProjection (e j))
    (d : ZMod N) (x c : E) (η : ℝ) (hη : 0 ≤ η)
    (hshift : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η) :
    let a := maskedTowerBand e (Equiv.addRight d) (fun j => finiteRowShiftIterate s j.val x) 0
    ‖(finiteRowShift s a - a) * c‖ ≤
      (2 * (N : ℝ) * η * ‖c‖ + ‖e 0 * c‖ + ‖e 1 * c‖) * ‖x‖ := by
  dsimp only
  let a := maskedTowerBand e (Equiv.addRight d) (fun j => finiteRowShiftIterate s j.val x) 0
  let b₀ := e d * finiteRowShiftIterate s N x * e 0
  let b₁ := e (1 + d) * finiteRowShiftIterate s 1 x * e 1
  let z := finiteRowShift s a - (a + b₀ - b₁)
  have hz : ‖z‖ ≤ 2 * (N : ℝ) * η * ‖x‖ :=
    maskedBand_shift_boundary_error hN s hs e he d x η hη hshift
  have hb₀ : ‖b₀ * c‖ ≤ ‖x‖ * ‖e 0 * c‖ := by
    have hprod : b₀ * c = (e d * finiteRowShiftIterate s N x) * (e 0 * c) := by
      dsimp only [b₀]; noncomm_ring
    rw [hprod]
    have hb : ‖e d * finiteRowShiftIterate s N x‖ ≤ ‖x‖ := by
      apply (norm_mul_le _ _).trans
      calc
        _ ≤ 1 * ‖x‖ := mul_le_mul (he d).norm_le (binaryRowIterate_norm_le s hs N x)
          (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hb₁ : ‖b₁ * c‖ ≤ ‖x‖ * ‖e 1 * c‖ := by
    have hprod : b₁ * c = (e (1 + d) * finiteRowShiftIterate s 1 x) * (e 1 * c) := by
      dsimp only [b₁]; noncomm_ring
    rw [hprod]
    have hb : ‖e (1 + d) * finiteRowShiftIterate s 1 x‖ ≤ ‖x‖ := by
      apply (norm_mul_le _ _).trans
      calc
        _ ≤ 1 * ‖x‖ := mul_le_mul (he (1 + d)).norm_le (binaryRowIterate_norm_le s hs 1 x)
          (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have heq : (finiteRowShift s a - a) * c = z * c + b₀ * c - b₁ * c := by
    dsimp only [z]
    noncomm_ring
  change ‖(finiteRowShift s a - a) * c‖ ≤ _
  rw [heq]
  calc
    _ ≤ (‖z * c‖ + ‖b₀ * c‖) + ‖b₁ * c‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((2 * (N : ℝ) * η * ‖x‖) * ‖c‖ + ‖x‖ * ‖e 0 * c‖) + ‖x‖ * ‖e 1 * c‖ :=
      add_le_add (add_le_add
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hz (norm_nonneg _))) hb₀) hb₁
    _ = _ := by ring

private lemma projection_mul_masked_sum {I : Type*} [Fintype I] [DecidableEq I]
    (e : I → E) (o j : I) (he : ∀ i, IsStarProjection (e i))
    (ho : ∀ i k, i ≠ k → e i * e k = 0) (w : I → ℝ) :
    e j * (∑ i, w i • maskedBandCoefficients e o i) =
      if j = o then 0 else w j • e j := by
  rw [Finset.mul_sum]
  have hsum : (∑ i, e j * (w i • maskedBandCoefficients e o i)) =
      e j * (w j • maskedBandCoefficients e o j) := by
    apply Finset.sum_eq_single j
    · intro i _ hij
      by_cases hi : i = o
      · simp only [maskedBandCoefficients, ite_eq_left hi, smul_zero, mul_zero]
      · simp only [maskedBandCoefficients, ite_eq_right hi, mul_smul_comm,
          ho j i (Ne.symm hij), smul_zero]
    · simp
  rw [hsum]
  by_cases hj : j = o
  · simp only [maskedBandCoefficients, ite_eq_left hj, smul_zero, mul_zero]
  · simp only [maskedBandCoefficients, ite_eq_right hj, mul_smul_comm,
      (he j).isIdempotentElem.eq]

/-- The removed cell annihilates both actual angular coefficients. Their
cell-one components are bounded by the first retained angle. -/
lemma maskedAngle_boundary_bounds {N : ℕ} [NeZero N] (hN : 1 < N)
    (e : ZMod N → E) (he : ∀ i, IsStarProjection (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0) (θ : ZMod N → ℝ) :
    e 0 * maskedAngleCos (maskedBandCoefficients e 0) θ = 0 ∧
      e 0 * maskedAngleSin (maskedBandCoefficients e 0) θ = 0 ∧
      ‖e 1 * maskedAngleCos (maskedBandCoefficients e 0) θ‖ ≤ |θ 1| ∧
      ‖e 1 * maskedAngleSin (maskedBandCoefficients e 0) θ‖ ≤ |θ 1| := by
  have : Fact (1 < N) := ⟨hN⟩
  have hc0 := projection_mul_masked_sum e 0 0 he ho (fun i => Real.cos (θ i) - 1)
  have hs0 := projection_mul_masked_sum e 0 0 he ho (fun i => Real.sin (θ i))
  have hc1 := projection_mul_masked_sum e 0 1 he ho (fun i => Real.cos (θ i) - 1)
  have hs1 := projection_mul_masked_sum e 0 1 he ho (fun i => Real.sin (θ i))
  simp only [ite_true] at hc0 hs0
  simp only [one_ne_zero, ite_false] at hc1 hs1
  refine ⟨hc0, hs0, ?_, ?_⟩
  · change ‖e 1 * (∑ i, (Real.cos (θ i) - 1) • maskedBandCoefficients e 0 i)‖ ≤ _
    rw [hc1, norm_smul, Real.norm_eq_abs]
    apply (mul_le_of_le_one_right (abs_nonneg _) (he 1).norm_le).trans
    simpa only [Real.cos_zero, sub_zero] using Real.abs_cos_sub_cos_le (θ 1) 0
  · change ‖e 1 * (∑ i, Real.sin (θ i) • maskedBandCoefficients e 0 i)‖ ≤ _
    rw [hs1, norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (he 1).norm_le).trans Real.abs_sin_le_abs

/-- For the actual sine profile, the exceptional-cell term is bounded by
the first retained angle, rather than by the norm of a whole projection. -/
lemma maskedBand_shift_sine_error {N : ℕ} [NeZero N] (hN : 1 < N)
    (s : Fin 2 → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (he : ∀ j, IsStarProjection (e j))
    (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (d : ZMod N) (x : E) (θ : ZMod N → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hshift : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η) :
    let a := maskedTowerBand e (Equiv.addRight d) (fun j => finiteRowShiftIterate s j.val x) 0
    ‖(finiteRowShift s a - a) * maskedAngleSin (maskedBandCoefficients e 0) θ‖ ≤
      (2 * (N : ℝ) * η + |θ 1|) * ‖x‖ := by
  dsimp only
  obtain ⟨_, hs0, _, hs1⟩ := maskedAngle_boundary_bounds hN e he ho θ
  have hn := maskedAngleSin_norm_le (maskedBandCoefficients e 0)
    (retainedCell_properties e 0 he ho).1 (retainedCell_properties e 0 he ho).2.2 θ
  apply (maskedBand_shift_times_bound hN s hs e he d x
    (maskedAngleSin (maskedBandCoefficients e 0) θ) η hη hshift).trans
  rw [hs0, norm_zero, add_zero]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
  exact add_le_add (mul_le_of_le_one_right (by positivity) hn) hs1

/-- The cosine-minus-one profile has the same actual boundary control. -/
lemma maskedBand_shift_cosine_error {N : ℕ} [NeZero N] (hN : 1 < N)
    (s : Fin 2 → E) (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (he : ∀ j, IsStarProjection (e j))
    (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (d : ZMod N) (x : E) (θ : ZMod N → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hshift : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η) :
    let a := maskedTowerBand e (Equiv.addRight d) (fun j => finiteRowShiftIterate s j.val x) 0
    ‖(finiteRowShift s a - a) * maskedAngleCos (maskedBandCoefficients e 0) θ‖ ≤
      (4 * (N : ℝ) * η + |θ 1|) * ‖x‖ := by
  dsimp only
  obtain ⟨hc0, _, hc1, _⟩ := maskedAngle_boundary_bounds hN e he ho θ
  have hn := maskedAngleCos_norm_le (maskedBandCoefficients e 0)
    (retainedCell_properties e 0 he ho).1 (retainedCell_properties e 0 he ho).2.2 θ
  apply (maskedBand_shift_times_bound hN s hs e he d x
    (maskedAngleCos (maskedBandCoefficients e 0) θ) η hη hshift).trans
  rw [hc0, norm_zero, add_zero]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
  have hmul := mul_le_mul_of_nonneg_left hn (show 0 ≤ 2 * (N : ℝ) * η by positivity)
  linarith

end WeakPureInfiniteness

end

end OAI

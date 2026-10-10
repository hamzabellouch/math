import OAI.Analysis.OInfinity.BandProducts

namespace OAI

/-! # Actual iterated rows with the cyclic boundary removed

The zero cell is removed explicitly. On the retained domain, the two
neighboring-depth bands have small Gram errors. Their cross term is
controlled by the actual inner-letter orthogonality relation, rather than
an assumed slow-variation property.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

def maskedBandCoefficients (x : I → E) (o : I) (i : I) : E :=
  if i = o then 0 else x i

def maskedTowerBand (e : I → E) (σ : Equiv.Perm I) (x : I → E) (o : I) : E :=
  towerBand e σ (maskedBandCoefficients x o)

lemma maskedTowerBand_right_support (e : I → E) (σ : Equiv.Perm I) (x : I → E)
    (o : I) (ho : ∀ i j, i ≠ j → e i * e j = 0) :
    maskedTowerBand e σ x o * (1 - e o) = maskedTowerBand e σ x o := by
  have hz : maskedTowerBand e σ x o * e o = 0 := by
    unfold maskedTowerBand towerBand
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hio : i = o
    · simp only [maskedBandCoefficients, ite_eq_left hio, mul_zero, zero_mul]
    · rw [mul_assoc _ (e i), ho i o hio, mul_zero]
  rw [mul_sub, mul_one, hz, sub_zero]

private lemma mask_projection_sum (e : I → E) (o : I)
    (he : ∀ i, e i * e i = e i) (hsum : (∑ i, e i) = 1) :
    towerBand e 1 (maskedBandCoefficients (fun _ => 1) o) = 1 - e o := by
  unfold towerBand
  have ht (i : I) : e ((1 : Equiv.Perm I) i) *
      maskedBandCoefficients (fun _ => (1 : E)) o i * e i =
        e i - if i = o then e o else 0 := by
    by_cases hio : i = o
    · subst i; simp only [maskedBandCoefficients, ite_true, mul_zero, zero_mul, sub_self]
    · simp only [maskedBandCoefficients, ite_eq_right hio, Equiv.Perm.one_apply, mul_one,
        he, sub_zero]
  simp only [ht, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, hsum]

lemma maskedTowerBand_gram_bound (e : I → E) (σ : Equiv.Perm I) (x : I → E)
    (o : I) (he : ∀ i, IsStarProjection (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0) (hsum : (∑ i, e i) = 1)
    (hx : ∀ i, star (x i) * x i = 1) (hxn : ∀ i, ‖x i‖ ≤ 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (htransport : ∀ i, ‖x i * e i - e (σ i) * x i‖ ≤ δ) :
    ‖star (maskedTowerBand e σ x o) * maskedTowerBand e σ x o - (1 - e o)‖ ≤ δ := by
  let y := maskedBandCoefficients x o
  let c : I → E := fun i => star (y i) * e (σ i) * y i
  let q := maskedBandCoefficients (fun _ : I => (1 : E)) o
  have hgram : star (maskedTowerBand e σ x o) * maskedTowerBand e σ x o =
      towerBand e 1 c := by
    unfold maskedTowerBand
    rw [towerBand_star e σ _ (fun i => (he i).isSelfAdjoint.star_eq),
      towerBand_mul e σ⁻¹ σ _ _ (fun i => (he i).isIdempotentElem.eq) ho]
    rw [inv_mul_cancel]
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rfl
  have hq : towerBand e 1 q = 1 - e o :=
    mask_projection_sum e o (fun i => (he i).isIdempotentElem.eq) hsum
  have hd : towerBand e 1 c - towerBand e 1 q = towerBand e 1 (fun i => c i - q i) := by
    simp only [towerBand, mul_sub, sub_mul, Finset.sum_sub_distrib]
  rw [hgram, ← hq, hd]
  apply towerBand_norm_le_of_sandwich e 1 _ he ho δ hδ
  intro i
  change ‖e i * (c i - q i) * e i‖ ≤ δ
  by_cases hio : i = o
  · simp only [c, y, q, maskedBandCoefficients, ite_eq_left hio, star_zero,
      zero_mul, mul_zero, sub_zero, norm_zero]
    exact hδ
  · have hy : y i = x i := ite_eq_right hio
    have hqi : q i = 1 := ite_eq_right hio
    have hp := (he i).isIdempotentElem.eq
    have hid : e i * (star (x i) * e (σ i) * x i - 1) * e i =
        (e i * star (x i)) * ((e (σ i) * x i - x i * e i) * e i) := by
      symm
      calc
        _ = e i * (star (x i) * e (σ i) * x i) * e i -
            e i * (star (x i) * x i) * (e i * e i) := by noncomm_ring
        _ = _ := by rw [hx i, hp]; noncomm_ring
    dsimp only [c]
    rw [hy, hqi, hid]
    have hn : ‖e i * star (x i)‖ ≤ 1 := by
      apply (norm_mul_le _ _).trans
      rw [norm_star]
      exact (mul_le_mul (he i).norm_le (hxn i) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
    have hb : ‖(e (σ i) * x i - x i * e i) * e i‖ ≤ δ := by
      apply (norm_mul_le _ _).trans
      exact (mul_le_of_le_one_right (norm_nonneg _) (he i).norm_le).trans
        (by simpa only [norm_sub_rev] using htransport i)
    exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hn).trans hb)

omit [Fintype I] [DecidableEq I] in
private lemma iterate_one (s : Fin 2 → E) (hsum : (∑ i, s i * star (s i)) = 1) (n : ℕ) :
    finiteRowShiftIterate s n 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [finiteRowShiftIterate, ih, finiteRowShift, mul_one] using hsum

omit [Fintype I] [DecidableEq I] in
private lemma iterate_isometry (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (x : E) (hx : star x * x = 1) (n : ℕ) :
    star (finiteRowShiftIterate s n x) * finiteRowShiftIterate s n x = 1 := by
  rw [finiteRowShiftIterate_star, ← binaryRowIterate_mul s hs, hx, iterate_one s hsum]

omit [Fintype I] [DecidableEq I] in
private lemma isometry_norm_bound (x : E) (hx : star x * x = 1) : ‖x‖ ≤ 1 := by
  have h := congrArg norm hx
  rw [CStarRing.norm_star_mul_self] at h
  have h1 : ‖(1 : E)‖ ≤ 1 := IsStarProjection.norm_le 1
    (isStarProjection_iff'.mpr ⟨by simp, by simp⟩)
  nlinarith [norm_nonneg x]

omit [Fintype I] [DecidableEq I] in
/-- A concrete word of degree at most two gives an almost isometric
masked band on exactly `1-e₀`. -/
lemma maskedIteratedWord_gram_bound {N : ℕ} [NeZero N] (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (e : ZMod N → E) (he : ∀ j, IsStarProjection (e j))
    (ho : ∀ i j, i ≠ j → e i * e j = 0) (hesum : (∑ i, e i) = 1)
    (η : ℝ) (hη : 0 ≤ η)
    (hshift : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η)
    (x : E) (hx : star x * x = 1) (d : ZMod N)
    (hxshift : ∀ j, ‖x * e j - e (j + d) * x‖ ≤ 2 * η) :
    let A := maskedTowerBand e (Equiv.addRight d)
      (fun j => finiteRowShiftIterate s j.val x) 0
    ‖star A * A - (1 - e 0)‖ ≤ (2 * (N : ℝ) + 2) * η := by
  dsimp only
  apply maskedTowerBand_gram_bound e (Equiv.addRight d) _ 0 he ho hesum
    (fun j => iterate_isometry s hs hsum x hx j.val)
    (fun j => isometry_norm_bound _ (iterate_isometry s hs hsum x hx j.val))
    _ (by positivity)
  intro j
  have h := binaryRowIterate_band_transport s hs e η hη hshift x d (2 * η) hxshift j.val j
  apply h.trans
  have hxn : ‖x‖ ≤ 1 := isometry_norm_bound x hx
  have hj : (j.val : ℝ) < N := by exact_mod_cast ZMod.val_lt j
  calc
    _ ≤ 2 * η + 2 * (j.val : ℝ) * η * 1 := by gcongr
    _ ≤ (2 * (N : ℝ) + 2) * η := by nlinarith

omit [Fintype I] [DecidableEq I] in
/-- The actual two-letter and one-letter bands have small cross Gram
on the retained cells. The cyclic zero cell is explicitly removed. -/
lemma maskedIteratedRows_cross_bound {N : ℕ} [NeZero N] (hN : 1 < N)
    (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (he : ∀ j, IsStarProjection (e j))
    (ho : ∀ j k, j ≠ k → e j * e k = 0)
    (η : ℝ) (hη : 0 ≤ η)
    (hshift : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η)
    (i r l : Fin 2) (hrl : r ≠ l) :
    let A := maskedTowerBand e (Equiv.addRight 2)
      (fun j => finiteRowShiftIterate s j.val (s i * s r)) 0
    let B := maskedTowerBand e (Equiv.addRight 1)
      (fun j => finiteRowShiftIterate s j.val (s l)) 0
    ‖star A * B‖ ≤ (2 * (N : ℝ) + 1) * η := by
  have : Fact (1 < N) := ⟨hN⟩
  dsimp only
  unfold maskedTowerBand
  rw [towerBand_star e (Equiv.addRight 2) _ (fun j => (he j).isSelfAdjoint.star_eq),
    towerBand_mul e (Equiv.addRight 2)⁻¹ (Equiv.addRight 1) _ _
      (fun j => (he j).isIdempotentElem.eq) ho]
  apply towerBand_norm_le_of_sandwich e _ _ he ho _ (by positivity)
  intro j
  have hp : (Equiv.addRight (2 : ZMod N))⁻¹ ((Equiv.addRight 1) j) = j - 1 := by
    simp only [Equiv.Perm.inv_def, Equiv.addRight_symm_apply, Equiv.coe_addRight]
    ring
  have hp' : (((Equiv.addRight (2 : ZMod N) : Equiv.Perm (ZMod N))⁻¹ *
      Equiv.addRight 1) : Equiv.Perm (ZMod N)) j = j - 1 := hp
  rw [hp, hp']
  change ‖e (j - 1) * (star (maskedBandCoefficients
      (fun k : ZMod N => finiteRowShiftIterate s k.val (s i * s r)) 0 (j - 1)) *
      e (j + 1) * maskedBandCoefficients
        (fun k : ZMod N => finiteRowShiftIterate s k.val (s l)) 0 j) * e j‖ ≤ _
  by_cases hj : j = 0
  · simp only [maskedBandCoefficients, ite_eq_left hj, mul_zero, zero_mul, norm_zero]
    positivity
  by_cases hj' : j - 1 = 0
  · simp only [maskedBandCoefficients, ite_eq_left hj', star_zero, zero_mul, mul_zero, norm_zero]
    positivity
  simp only [maskedBandCoefficients, ite_eq_right hj, ite_eq_right hj']
  have hv : (j - 1).val + 1 = j.val := by
    have hpos : 1 ≤ j.val := Nat.succ_le_of_lt (ZMod.val_pos.mpr hj)
    rw [ZMod.val_sub (a := j) (b := 1) (by simpa only [ZMod.val_one] using hpos),
      ZMod.val_one]
    omega
  have h := binaryRowIterate_mixed_corner_bound s hs e he η hη hshift
    (j - 1).val i r l hrl j
  rw [hv] at h
  have heq : e (j - 1) * (star (finiteRowShiftIterate s (j - 1).val (s i * s r)) *
      e (j + 1) * finiteRowShiftIterate s j.val (s l)) * e j =
      e (j - 1) * (star (finiteRowShiftIterate s (j - 1).val (s i * s r)) *
        e (j + 1) * finiteRowShiftIterate s j.val (s l) * e j) := by noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖star (finiteRowShiftIterate s (j - 1).val (s i * s r)) *
        e (j + 1) * finiteRowShiftIterate s j.val (s l) * e j‖ :=
      (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (he (j - 1)).norm_le)
    _ ≤ (2 * ((j - 1).val : ℝ) + 3) * η := h
    _ ≤ (2 * (N : ℝ) + 1) * η := by
      apply mul_le_mul_of_nonneg_right _ hη
      have hlt : (j - 1).val < N := ZMod.val_lt _
      have hle : (j - 1).val + 1 ≤ N := hlt
      exact_mod_cast (by omega : 2 * (j - 1).val + 3 ≤ 2 * N + 1)

end WeakPureInfiniteness

end

end OAI

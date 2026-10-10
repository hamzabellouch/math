import OAI.Analysis.OInfinity.BandOperators
import OAI.Analysis.OInfinity.IteratedBandTransport

namespace OAI

/-! # Exact band products and the actual adjacent-depth corner

Products sample their first coefficient at the shifted index. The final
lemma uses the concrete Cuntz relation at neighboring depths, with its
inner-letter orthogonality condition. It is local in the tower cell; no
cyclic boundary cell is silently identified with the next depth.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma towerBand_star (e : I → E) (σ : Equiv.Perm I) (x : I → E)
    (he : ∀ i, star (e i) = e i) :
    star (towerBand e σ x) = towerBand e σ⁻¹ (fun i => star (x (σ⁻¹ i))) := by
  change star (∑ i, e (σ i) * x i * e i) =
    ∑ i, e (σ⁻¹ i) * star (x (σ⁻¹ i)) * e i
  rw [star_sum]
  calc
    _ = ∑ i, e i * star (x i) * e (σ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [star_mul, he, mul_assoc]
    _ = _ := by
      apply Fintype.sum_equiv σ
      intro i
      simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]

omit [DecidableEq I] in
/-- The first coefficient is evaluated at `τ i`, rather than `i`. -/
lemma towerBand_mul (e : I → E) (σ τ : Equiv.Perm I) (x y : I → E)
    (hee : ∀ i, e i * e i = e i)
    (ho : ∀ i j, i ≠ j → e i * e j = 0) :
    towerBand e σ x * towerBand e τ y =
      towerBand e (σ * τ) (fun i => x (τ i) * e (τ i) * y i) := by
  classical
  change (∑ i, e (σ i) * x i * e i) * (∑ j, e (τ j) * y j * e j) = _
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  change (∑ j, ∑ i, (e (σ i) * x i * e i) * (e (τ j) * y j * e j)) = _
  unfold towerBand
  apply Finset.sum_congr rfl
  intro j hj
  have hterm (i : I) (hij : i ≠ τ j) :
      (e (σ i) * x i * e i) * (e (τ j) * y j * e j) = 0 := by
    calc
      _ = e (σ i) * x i * (e i * e (τ j)) * y j * e j := by noncomm_ring
      _ = 0 := by rw [ho i (τ j) hij]; simp
  rw [Finset.sum_eq_single (τ j) (fun i _ hi => hterm i hi) (by simp)]
  simp only [Equiv.Perm.mul_apply]
  calc
    _ = e (σ (τ j)) * x (τ j) * (e (τ j) * e (τ j)) * y j * e j := by
      noncomm_ring
    _ = _ := by rw [hee]; noncomm_ring

/-- The product estimate applies to the actual shifted coefficient. -/
lemma towerBand_mul_norm_le (e : I → E) (σ τ : Equiv.Perm I) (x y : I → E)
    (he : ∀ i, IsStarProjection (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hxy : ∀ i, ‖x (τ i) * e (τ i) * y i‖ ≤ M) :
    ‖towerBand e σ x * towerBand e τ y‖ ≤ M := by
  rw [towerBand_mul e σ τ x y (fun i => (he i).isIdempotentElem.eq) ho]
  exact towerBand_norm_le e (σ * τ) _ he ho M hM hxy

/-- It suffices to bound the actual corner of each coefficient. -/
lemma towerBand_norm_le_of_sandwich (e : I → E) (σ : Equiv.Perm I) (x : I → E)
    (he : ∀ i, IsStarProjection (e i))
    (ho : ∀ i j, i ≠ j → e i * e j = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hx : ∀ i, ‖e (σ i) * x i * e i‖ ≤ M) :
    ‖towerBand e σ x‖ ≤ M := by
  have h : towerBand e σ x = towerBand e σ (fun i => e (σ i) * x i * e i) := by
    unfold towerBand
    apply Finset.sum_congr rfl
    intro i hi
    symm
    calc
      _ = (e (σ i) * e (σ i)) * x i * (e i * e i) := by noncomm_ring
      _ = _ := by rw [(he (σ i)).isIdempotentElem.eq, (he i).isIdempotentElem.eq]
  rw [h]
  exact towerBand_norm_le e σ _ he ho M hM hx

omit [Fintype I] [DecidableEq I] in
private lemma mixed_corner_norm_le (a b f p : E) (hzero : star a * b = 0)
    (han : ‖a‖ ≤ 1) (hpp : p * p = p) (hpn : ‖p‖ ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (hb : ‖b * p - f * b‖ ≤ η) :
    ‖star a * f * b * p‖ ≤ η := by
  have hid : star a * f * b * p = star a * ((f * b - b * p) * p) := by
    have hz : star a * (b * p) = 0 := by rw [← mul_assoc, hzero, zero_mul]
    rw [sub_mul, mul_assoc b p p, hpp, mul_sub, hz, sub_zero]
    noncomm_ring
  rw [hid]
  calc
    _ ≤ ‖star a‖ * (‖f * b - b * p‖ * ‖p‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * (η * 1) := by
      apply mul_le_mul
      · simpa only [norm_star] using han
      · exact mul_le_mul (by simpa only [norm_sub_rev] using hb) hpn (norm_nonneg _) hη
      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · norm_num
    _ = η := by ring

omit [Fintype I] [DecidableEq I] in
private lemma binaryBand_row_norm (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) (i : Fin 2) :
    ‖s i‖ ≤ 1 := by
  have h := congrArg norm (hs i i)
  simp only [ite_true, CStarRing.norm_star_mul_self] at h
  have hn : ‖(1 : E)‖ ≤ 1 := IsStarProjection.norm_le 1
    (isStarProjection_iff'.mpr ⟨by simp, by simp⟩)
  nlinarith [norm_nonneg (s i)]

omit [Fintype I] [DecidableEq I] in
/-- The overlap of the two actual neighboring-depth bands is small when
`r ≠ l`. The depth `n+1` is literal, including at a tower boundary. -/
lemma binaryRowIterate_mixed_corner_bound {N : ℕ} (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (e : ZMod N → E) (he : ∀ j, IsStarProjection (e j))
    (η : ℝ) (hη : 0 ≤ η)
    (hshift : ∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η)
    (n : ℕ) (i r l : Fin 2) (hrl : r ≠ l) (j : ZMod N) :
    ‖star (finiteRowShiftIterate s n (s i * s r)) * e (j + 1) *
        finiteRowShiftIterate s (n + 1) (s l) * e j‖ ≤
      (2 * (n : ℝ) + 3) * η := by
  have han : ‖finiteRowShiftIterate s n (s i * s r)‖ ≤ 1 := by
    apply (binaryRowIterate_norm_le s hs n _).trans
    exact (norm_mul_le _ _).trans
      ((mul_le_mul (binaryBand_row_norm s hs i) (binaryBand_row_norm s hs r)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1))
  have hzero : star (finiteRowShiftIterate s n (s i * s r)) *
      finiteRowShiftIterate s (n + 1) (s l) = 0 := by
    simpa only [ite_eq_right hrl] using binaryRowIterate_mixed_gram s hs n i r l
  have hb := binaryRowIterate_band_transport s hs e η hη hshift (s l) 1 η
    (cyclic_row_generator_transport s hs e η hshift l) (n + 1) j
  have hbn : ‖s l‖ ≤ 1 := binaryBand_row_norm s hs l
  have hbound : ‖finiteRowShiftIterate s (n + 1) (s l) * e j -
      e (j + 1) * finiteRowShiftIterate s (n + 1) (s l)‖ ≤
        (2 * (n : ℝ) + 3) * η := by
    apply hb.trans
    calc
      _ ≤ η + 2 * ((n + 1 : ℕ) : ℝ) * η * 1 := by gcongr
      _ = _ := by push_cast; ring
  exact mixed_corner_norm_le _ _ _ _ hzero han (he j).isIdempotentElem.eq
    (he j).norm_le _ (by positivity) hbound

end WeakPureInfiniteness

end

end OAI

import OAI.Analysis.WeakInfiniteness.CuntzPairCorrection
import OAI.Analysis.OInfinity.MaskedBandRows

namespace OAI

/-! # Gram correction with a common initial projection

The removed cyclic cell is not filled. Adding its complementary projection
only to the square Gram matrix permits inverse-square-root normalization;
the corrected rectangular row still has the original initial projection.
-/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

local instance relativeGramRealModule (n : Type*) [Fintype n] :
    Module ℝ (CStarMatrix n n E) := Module.complexToReal _
local instance relativeGramRealAlgebra (n : Type*) [Fintype n] [DecidableEq n] :
    Algebra ℝ (CStarMatrix n n E) := Algebra.complexToReal

/-- Rectangular normalization preserves an exact right support. -/
lemma exists_relative_rectangular_isometry_near
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (u : CStarMatrix m n E) (q : CStarMatrix n n E),
      IsStarProjection q → u * q = u → ‖u‖ ≤ M →
      ‖u.conjTranspose * u - q‖ < δ →
      ∃ v : CStarMatrix m n E,
        v * q = v ∧ v.conjTranspose * v = q ∧ ‖v - u‖ < ε := by
  obtain ⟨δ, hδ, hcorr⟩ := exists_inverse_sqrt_tolerance
    (A := CStarMatrix n n E) (ε / (M + 1)) (div_pos hε (by linarith))
  refine ⟨δ, hδ, ?_⟩
  intro u q hq huq hu hgram
  let h := u.conjTranspose * u
  let g := h + (1 - q)
  have hhq : h * q = h := by
    change (u.conjTranspose * u) * q = u.conjTranspose * u
    rw [rectangular_mul_assoc, huq]
  have hqh : q * h = h := by
    have hqu : q * u.conjTranspose = u.conjTranspose := by
      have hz := congrArg (fun a : CStarMatrix m n E => a.conjTranspose) huq
      rw [rectangular_star_mul] at hz
      change star q * u.conjTranspose = u.conjTranspose at hz
      rwa [hq.isSelfAdjoint.star_eq] at hz
    change q * (u.conjTranspose * u) = u.conjTranspose * u
    rw [← rectangular_mul_assoc, hqu]
  have hgq : g * q = h := by
    change (h + (1 - q)) * q = h
    rw [add_mul, hhq, hq.one_sub_mul_self, add_zero]
  have hqg : q * g = h := by
    change q * (h + (1 - q)) = h
    rw [mul_add, hqh, hq.mul_one_sub_self, add_zero]
  have hg0 : 0 ≤ g := add_nonneg (rectangular_initial_nonneg u) hq.one_sub.nonneg
  have hgn : ‖g - 1‖ < δ := by
    have he : g - 1 = h - q := by dsimp only [g]; noncomm_ring
    rw [he]
    exact hgram
  obtain ⟨hgp, hkn⟩ := hcorr g hg0 hgn
  let k : CStarMatrix n n E := g ^ (-(1 / 2) : ℝ)
  have hk : star k = k := (CFC.rpow_nonneg (a := g)).star_eq
  have hkg : k * g * k = 1 := CFC.conjugate_rpow_neg_one_half g hgp
  have hkq : k * q = q * k := by
    have hcomm : Commute g q := hgq.trans hqg.symm
    exact (hcomm.cfc_nnreal (fun t => t ^ (-(1 / 2) : ℝ))).eq
  have hkh : k * h * k = q := by
    calc
      k * h * k = k * (q * g * q) * k := by rw [hqg, hhq]
      _ = q * (k * g * k) * q := by
        calc
          _ = (k * q) * g * (q * k) := by noncomm_ring
          _ = (q * k) * g * (k * q) := by rw [hkq]
          _ = _ := by noncomm_ring
      _ = q := by rw [hkg, mul_one, hq.isIdempotentElem.eq]
  refine ⟨u * k, ?_, ?_, ?_⟩
  · calc
      (u * k) * q = u * (k * q) := rectangular_mul_assoc _ _ _
      _ = u * (q * k) := by rw [hkq]
      _ = u * k := by rw [← rectangular_mul_assoc, huq]
  · rw [rectangular_initial_mul, hk]
    exact hkh
  · have hu1 : u * (1 : CStarMatrix n n E) = u := by
      ext i j
      change (∑ l, u i l * (if l = j then 1 else 0)) = u i j
      simp
    have hsub : u * (k - 1) = u * k - u * (1 : CStarMatrix n n E) := by
      ext i j
      change (∑ l, u i l * (k l j - (1 : CStarMatrix n n E) l j)) =
        (∑ l, u i l * k l j) - ∑ l, u i l * (1 : CStarMatrix n n E) l j
      simp only [mul_sub, Finset.sum_sub_distrib]
    have he : u * k - u = u * (k - 1) := by rw [hsub, hu1]
    rw [he]
    calc
      _ ≤ ‖u‖ * ‖k - 1‖ := rectangular_norm_mul_le _ _
      _ ≤ M * ‖k - 1‖ := mul_le_mul_of_nonneg_right hu (norm_nonneg _)
      _ < (M + 1) * (ε / (M + 1)) := by
        change ‖k - 1‖ < ε / (M + 1) at hkn
        have hp : 0 < ε / (M + 1) := div_pos hε (by linarith)
        nlinarith [norm_nonneg (k - 1)]
      _ = ε := mul_div_cancel₀ _ (by linarith : M + 1 ≠ 0)

/-- The common initial projection of a two-column row. -/
def relativePairProjection (p : E) : CStarMatrix (Fin 2) (Fin 2) E :=
  CStarMatrix.ofMatrix (fun i j => if i = j then p else 0)

omit [PartialOrder E] [StarOrderedRing E] in
lemma relativePairProjection_apply (p : E) (i j : Fin 2) :
    relativePairProjection p i j = if i = j then p else 0 := rfl

omit [PartialOrder E] [StarOrderedRing E] in
lemma relativePairProjection_isStarProjection (p : E) (hp : IsStarProjection p) :
    IsStarProjection (relativePairProjection p) := by
  apply isStarProjection_iff'.mpr
  constructor
  · ext i j
    change (∑ k : Fin 2, (if i = k then p else 0) * (if k = j then p else 0)) =
      (if i = j then p else 0)
    fin_cases i <;> fin_cases j <;>
      simp [hp.isIdempotentElem.eq]
  · ext i j
    change star (if j = i then p else 0) = if i = j then p else 0
    fin_cases i <;> fin_cases j <;> simp [hp.isSelfAdjoint.star_eq]

omit [PartialOrder E] [StarOrderedRing E] in
lemma cuntzPairRow_relative_support (a b p : E) (ha : a * p = a) (hb : b * p = b) :
    cuntzPairRow a b * relativePairProjection p = cuntzPairRow a b := by
  ext i j
  change (∑ k : Fin 2, ![a, b] k * (if k = j then p else 0)) = ![a, b] j
  fin_cases j <;> simp [ha, hb]

lemma cuntzPairRow_relative_gram_bound (a b p : E) :
    ‖(cuntzPairRow a b).conjTranspose * cuntzPairRow a b - relativePairProjection p‖ ≤
      ‖star a * a - p‖ + ‖star b * b - p‖ + 2 * ‖star a * b‖ := by
  have h := rectangular_norm_le_sum_entries
    ((cuntzPairRow a b).conjTranspose * cuntzPairRow a b - relativePairProjection p)
  have hnorm : ‖star b * a‖ = ‖star a * b‖ := by
    rw [← norm_star (star a * b), star_mul, star_star]
  simp only [Fin.sum_univ_two, CStarMatrix.sub_apply, cuntzPairRow_initial_entry,
    Matrix.cons_val_zero, Matrix.cons_val_one, relativePairProjection_apply,
    ite_true, show ¬ (0 : Fin 2) = 1 by decide, show ¬ (1 : Fin 2) = 0 by decide,
    ite_false, sub_zero, hnorm] at h
  linarith

/-- Two approximately orthogonal supported columns can be corrected without
filling the removed projection. -/
lemma exists_relative_cuntzPair_near (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b p : E,
      IsStarProjection p → a * p = a → b * p = b → ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖star a * a - p‖ < δ → ‖star b * b - p‖ < δ → ‖star a * b‖ < δ →
      ∃ r t : E, r * p = r ∧ t * p = t ∧
        star r * r = p ∧ star t * t = p ∧ star r * t = 0 ∧
        ‖r - a‖ < ε ∧ ‖t - b‖ < ε := by
  obtain ⟨δ, hδ, hcorr⟩ := exists_relative_rectangular_isometry_near (E := E)
    (m := Fin 1) (n := Fin 2) 2 ε (by norm_num) hε
  refine ⟨δ / 4, by positivity, ?_⟩
  intro a b p hp ha hb han hbn haa hbb hab
  have hu : ‖cuntzPairRow a b‖ ≤ 2 :=
    (norm_cuntzPairRow_le a b).trans (by linarith)
  have hg : ‖(cuntzPairRow a b).conjTranspose * cuntzPairRow a b -
      relativePairProjection p‖ < δ := by
    have hh := cuntzPairRow_relative_gram_bound a b p
    linarith
  obtain ⟨v, hvp, hvg, hvn⟩ := hcorr (cuntzPairRow a b) (relativePairProjection p)
    (relativePairProjection_isStarProjection p hp) (cuntzPairRow_relative_support a b p ha hb) hu hg
  have hsup (j : Fin 2) : v 0 j * p = v 0 j := by
    have hh := congrArg (fun w : CStarMatrix (Fin 1) (Fin 2) E => w 0 j) hvp
    change (∑ k : Fin 2, v 0 k * (if k = j then p else 0)) = v 0 j at hh
    fin_cases j <;> simpa [Fin.sum_univ_two] using hh
  have hgr (i j : Fin 2) : star (v 0 i) * v 0 j = if i = j then p else 0 := by
    have hh := congrArg (fun w : CStarMatrix (Fin 2) (Fin 2) E => w i j) hvg
    change (∑ _k : Fin 1, star (v 0 i) * v 0 j) = (if i = j then p else 0) at hh
    simpa only [Fin.sum_univ_one] using hh
  refine ⟨v 0 0, v 0 1, hsup 0, hsup 1, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hgr 0 0
  · simpa using hgr 1 1
  · simpa using hgr 0 1
  · exact (CStarMatrix.norm_entry_le_norm (M := v - cuntzPairRow a b) (i := 0) (j := 0)).trans_lt hvn
  · exact (CStarMatrix.norm_entry_le_norm (M := v - cuntzPairRow a b) (i := 0) (j := 1)).trans_lt hvn

omit [PartialOrder E] [StarOrderedRing E] in
private lemma relativeGram_word_isometry (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0) :
    star (s 0 * s 0) * (s 0 * s 0) = 1 := by
  rw [star_mul]
  calc
    _ = star (s 0) * (star (s 0) * s 0) * s 0 := by noncomm_ring
    _ = 1 := by simp only [hs, ite_true, mul_one]

omit [PartialOrder E] [StarOrderedRing E] in
private lemma relativeGram_iterate_isometry (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1) (x : E) (hx : star x * x = 1) (n : ℕ) :
    star (finiteRowShiftIterate s n x) * finiteRowShiftIterate s n x = 1 := by
  have h1 : finiteRowShiftIterate s n 1 = 1 := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [finiteRowShiftIterate, ih, finiteRowShift, mul_one] using hsum
  rw [finiteRowShiftIterate_star, ← binaryRowIterate_mul s hs, hx, h1]

omit [PartialOrder E] [StarOrderedRing E] in
private lemma relativeGram_isometry_norm (x : E) (hx : star x * x = 1) : ‖x‖ ≤ 1 := by
  have h := congrArg norm hx
  rw [CStarRing.norm_star_mul_self] at h
  have h1 : ‖(1 : E)‖ ≤ 1 := (IsStarProjection.one E).norm_le
  nlinarith [norm_nonneg x]

/-- The actual iterated two-letter and one-letter bands admit exact relative
orthogonalization, with arbitrarily small correction. The cell zero stays
removed from both initial projections. -/
lemma exists_corrected_masked_binary_rows {N : ℕ} [NeZero N] (hN : 1 < N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (s : Fin 2 → E),
      (∀ i j, star (s i) * s j = if i = j then 1 else 0) →
      (∑ i, s i * star (s i)) = 1 →
      ∀ e : ZMod N → E, (∀ j, IsStarProjection (e j)) →
      (∀ j k, j ≠ k → e j * e k = 0) → (∑ j, e j) = 1 →
      (∀ j, ‖finiteRowShift s (e j) - e (j + 1)‖ ≤ η) →
      let a := maskedTowerBand e (Equiv.addRight 2)
        (fun j => finiteRowShiftIterate s j.val (s 0 * s 0)) 0
      let b := maskedTowerBand e (Equiv.addRight 1)
        (fun j => finiteRowShiftIterate s j.val (s 1)) 0
      ∃ r t : E, r * (1 - e 0) = r ∧ t * (1 - e 0) = t ∧
        star r * r = 1 - e 0 ∧ star t * t = 1 - e 0 ∧ star r * t = 0 ∧
        ‖r - a‖ < ε ∧ ‖t - b‖ < ε := by
  obtain ⟨δ, hδ, hcorr⟩ := exists_relative_cuntzPair_near (E := E) ε hε
  let η := δ / (2 * (N : ℝ) + 3)
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro s hs hsum e he ho hesum hshift
  dsimp only
  have hword := relativeGram_word_isometry s hs
  have hsingle : star (s 1) * s 1 = 1 := by simpa only [ite_true] using hs 1 1
  have hbound (x : E) (hx : star x * x = 1) (d : ZMod N) :
      ‖maskedTowerBand e (Equiv.addRight d)
        (fun j => finiteRowShiftIterate s j.val x) 0‖ ≤ 1 := by
    apply towerBand_norm_le e (Equiv.addRight d) _ he ho 1 zero_le_one
    intro j
    by_cases hj : j = 0
    · simp only [maskedBandCoefficients, ite_eq_left hj, norm_zero, zero_le_one]
    · simp only [maskedBandCoefficients, ite_eq_right hj]
      exact relativeGram_isometry_norm _ (relativeGram_iterate_isometry s hs hsum x hx j.val)
  have hless : (2 * (N : ℝ) + 2) * η < δ := by
    have heq : (2 * (N : ℝ) + 3) * η = δ := by
      dsimp only [η]
      exact mul_div_cancel₀ _ (by positivity)
    nlinarith
  apply hcorr _ _ _ (he 0).one_sub
    (maskedTowerBand_right_support e _ _ 0 ho)
    (maskedTowerBand_right_support e _ _ 0 ho)
    (hbound _ hword _) (hbound _ hsingle _)
  · exact (maskedIteratedWord_gram_bound s hs hsum e he ho hesum η hη.le hshift
      (s 0 * s 0) hword 2 (cyclic_row_two_letter_transport s hs e η hshift 0 0)).trans_lt hless
  · apply (maskedIteratedWord_gram_bound s hs hsum e he ho hesum η hη.le hshift
      (s 1) hsingle 1 ?_).trans_lt hless
    intro j
    exact (cyclic_row_generator_transport s hs e η hshift 1 j).trans (by linarith)
  · apply (maskedIteratedRows_cross_bound hN s hs e he ho η hη.le hshift 0 0 1 (by decide)).trans_lt
    exact lt_of_le_of_lt (by nlinarith) hless

/-- An actual cyclic partition supplies the small Gram errors; no tower
or exact orthogonal-row premise is retained in this conclusion. -/
lemma exists_masked_binary_rotation_rows (s : Fin 2 → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hsum : (∑ i, s i * star (s i)) = 1)
    (m : ℕ) (hm : 1 < 2 ^ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ (e : ZMod (2 ^ m) → E) (r t : E),
      (∀ j, IsStarProjection (e j)) ∧
      (∀ j k, j ≠ k → e j * e k = 0) ∧ (∑ j, e j) = 1 ∧
      r * (1 - e 0) = r ∧ t * (1 - e 0) = t ∧
      star r * r = 1 - e 0 ∧ star t * t = 1 - e 0 ∧ star r * t = 0 ∧
      ‖r - maskedTowerBand e (Equiv.addRight 2)
        (fun j => finiteRowShiftIterate s j.val (s 0 * s 0)) 0‖ < ε ∧
      ‖t - maskedTowerBand e (Equiv.addRight 1)
        (fun j => finiteRowShiftIterate s j.val (s 1)) 0‖ < ε := by
  have : IsClosed ((⊤ : StarSubalgebra ℂ E) : Set E) := isClosed_univ
  obtain ⟨η, hη, hcorr⟩ := exists_corrected_masked_binary_rows (E := E) hm ε hε
  obtain ⟨e, _hem, he, hesum, ho, hshift⟩ :=
    exists_binary_cyclic_partition_in (⊤ : StarSubalgebra ℂ E) s hs hsum
      (fun _ => by simp) m η hη
  obtain ⟨r, t, hr, ht, hrr, htt, hrt, hra, htb⟩ :=
    hcorr s hs hsum e he ho hesum (fun j => (hshift j).le)
  exact ⟨e, r, t, he, ho, hesum, hr, ht, hrr, htt, hrt, hra, htb⟩

end WeakPureInfiniteness

end

end OAI

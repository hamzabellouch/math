import OAI.NumberTheory.TwoPoint.Bounds.SplitBadWordSum
import OAI.NumberTheory.TwoPoint.Bounds.BadEventDecay

namespace OAI

/-!
# The cost of the complete short-word catalog

Numerical primes are summed by reciprocal weight, rather than counted as
additional symbols.  This leaves only signs, equality classes, row records,
and tuple/padding flags.  The bound includes every length and every slot
count up to the stated budgets, including invalid codes.
-/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace CrudeWordCode

variable {R N : ℕ}

/-- The finite cost left after one nondegenerate prime relation is imposed. -/
noncomputable def badReciprocalCost (c : CrudeWordCode R N R) (VP VQ : ℝ) : ℝ :=
  (Fintype.card c.tupleClasses ^ 2 * (R + 1) ^ 2 : ℕ) *
    VP ^ Fintype.card c.tupleClasses *
    VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}

lemma badReciprocalCost_nonneg (c : CrudeWordCode R N R) {VP VQ : ℝ}
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ) : 0 ≤ c.badReciprocalCost VP VQ := by
  unfold badReciprocalCost
  positivity

lemma tuple_padding_class_count (c : CrudeWordCode R N R) :
    Fintype.card c.tupleClasses +
      Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} =
        Fintype.card c.usedClasses := by
  rw [Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le (fun z => z ∈ c.tupleClasses))

lemma class_count_le_slots (c : CrudeWordCode R N R) :
    Fintype.card c.tupleClasses +
      Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} ≤ N := by
  rw [c.tuple_padding_class_count]
  simpa only [Fintype.card_fin] using
    (Fintype.card_subtype_le (fun z : Fin N => z ∈ c.usedClasses))

/-- Tuple and padding classes together use at most one reciprocal mass per slot. -/
lemma class_mass_le (c : CrudeWordCode R N R) {VP VQ A : ℝ}
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ) (hPA : VP ≤ A) (hQA : VQ ≤ A)
    (hA : 1 ≤ A) :
    VP ^ Fintype.card c.tupleClasses *
      VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} ≤ A ^ N := by
  calc
    _ ≤ A ^ Fintype.card c.tupleClasses *
        A ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} :=
      mul_le_mul (pow_le_pow_left₀ hP hPA _) (pow_le_pow_left₀ hQ hQA _)
        (pow_nonneg hQ _) (pow_nonneg (zero_le_one.trans hA) _)
    _ = A ^ (Fintype.card c.tupleClasses +
        Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}) := (pow_add _ _ _).symm
    _ ≤ A ^ N := pow_le_pow_right₀ hA c.class_count_le_slots

end CrudeWordCode

/-- All lengths, all actual slot counts, and all finite equality codes. -/
noncomputable def badCatalogCost (s T : ℕ) (VP VQ : ℝ) : ℝ :=
  ∑ R : Fin (s + 1), ∑ N : Fin (T + 1),
    ∑ c : CrudeWordCode R.val N.val R.val, c.badReciprocalCost VP VQ

lemma short_log_le_square (s : ℕ) (L : ℝ) (hs : 1 ≤ s)
    (hlog : 1 ≤ Real.log L) : Real.log L ≤ s * (Real.log L) ^ 2 := by
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsq : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hsr) (sq_nonneg (Real.log L))]

lemma short_polynomial_exp_bound (s k : ℕ) (L : ℝ) (hs : 1 ≤ s)
    (hL : 0 < L) (hlog : 1 ≤ Real.log L) :
    L ^ k ≤ Real.exp ((k : ℝ) * s * (Real.log L) ^ 2) := by
  calc
    _ = Real.exp ((k : ℝ) * Real.log L) := by
      rw [Real.exp_nat_mul, Real.exp_log hL]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (short_log_le_square s L hs hlog)
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      nlinarith

/-- Unlike the coarser pattern estimate, this bound does not need `R ≤ N`;
empty or invalid codes may therefore be retained in the catalog. -/
lemma short_crudeWordCode_bound (R N s : ℕ) (L C : ℝ)
    (hlog : 1 ≤ Real.log L) (hR : R ≤ s)
    (hslots : (N : ℝ) ≤ C * s * Real.log L)
    (hN : (N : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hspoly : (s : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (CrudeWordCode R N R) : ℝ) ≤
      Real.exp ((1 + 5 * C) * s * (Real.log L) ^ 2) := by
  have hlog2 : Real.log 2 ≤ Real.log L := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogN : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < N + 1) hN
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hRpoly : (R : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
    have hr : (R : ℝ) ≤ s := by exact_mod_cast hR
    linarith
  have hlogR : Real.log ((R : ℝ) + 1) ≤ 2 * Real.log L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < R + 1) hRpoly
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have h1 : (R : ℝ) * Real.log 2 ≤ s * Real.log L :=
    mul_le_mul (by exact_mod_cast hR) hlog2
      (Real.log_nonneg (by norm_num)) (Nat.cast_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have h3 := mul_le_mul_of_nonneg_left hlogR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have h4 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have h5 := mul_le_mul_of_nonneg_right hslots (show 0 ≤ Real.log L by linarith)
  have h6 : (s : ℝ) * Real.log L ≤ s * (Real.log L) ^ 2 := by
    have hh : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
  apply (card_crudeWordCode_exp R N R).trans
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The reciprocal masses and the choice of one relation cost only an
additional `exp ((8 + 2 C) s log² L)` for a fixed code. -/
lemma short_badReciprocalCost_bound {R N s : ℕ} (c : CrudeWordCode R N R)
    (VP VQ L C : ℝ) (hs : 1 ≤ s) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hR : R ≤ s) (hslots : (N : ℝ) ≤ C * s * Real.log L)
    (hN : (N : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hspoly : (s : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ)
    (hPupper : VP ≤ L ^ (2 : ℕ)) (hQupper : VQ ≤ L ^ (2 : ℕ)) :
    c.badReciprocalCost VP VQ ≤
      Real.exp ((8 + 2 * C) * s * (Real.log L) ^ 2) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have htu : Fintype.card c.tupleClasses ≤ N := by
    have hh := c.class_count_le_slots
    omega
  have ht : (Fintype.card c.tupleClasses : ℝ) ≤ L ^ (2 : ℕ) := by
    have hh : (Fintype.card c.tupleClasses : ℝ) ≤ N := by exact_mod_cast htu
    linarith
  have hr : (R : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
    have hh : (R : ℝ) ≤ s := by exact_mod_cast hR
    linarith
  have hmeta : (Fintype.card c.tupleClasses ^ 2 * (R + 1) ^ 2 : ℕ) ≤
      Real.exp ((8 : ℝ) * s * (Real.log L) ^ 2) := by
    calc
      _ = (Fintype.card c.tupleClasses : ℝ) ^ 2 * ((R : ℝ) + 1) ^ 2 := by
        push_cast
        rfl
      _ ≤ (L ^ (2 : ℕ)) ^ 2 * (L ^ (2 : ℕ)) ^ 2 := by gcongr
      _ = L ^ (8 : ℕ) := by ring
      _ ≤ _ := short_polynomial_exp_bound s 8 L hs hLp hlog
  have hmass : VP ^ Fintype.card c.tupleClasses *
      VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} ≤
        Real.exp (2 * C * s * (Real.log L) ^ 2) := by
    calc
      _ ≤ (L ^ (2 : ℕ)) ^ N :=
        c.class_mass_le hP hQ hPupper hQupper (one_le_pow₀ hL)
      _ = Real.exp ((N : ℝ) * (2 * Real.log L)) := by
        rw [Real.exp_nat_mul]
        congr 1
        rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
          Real.exp_add, Real.exp_log hLp]
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hslots
          (show 0 ≤ 2 * Real.log L by linarith)
        nlinarith
  calc
    c.badReciprocalCost VP VQ =
        (Fintype.card c.tupleClasses ^ 2 * (R + 1) ^ 2 : ℕ) *
          (VP ^ Fintype.card c.tupleClasses *
            VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}) := by
      unfold CrudeWordCode.badReciprocalCost
      ring
    _ ≤ Real.exp ((8 : ℝ) * s * (Real.log L) ^ 2) *
        Real.exp (2 * C * s * (Real.log L) ^ 2) :=
      mul_le_mul hmeta hmass (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Sum over every code of one fixed length and slot count. -/
lemma short_badCode_sum_bound (R N s : ℕ) (VP VQ L C : ℝ)
    (hs : 1 ≤ s) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hR : R ≤ s) (hslots : (N : ℝ) ≤ C * s * Real.log L)
    (hN : (N : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hspoly : (s : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ)
    (hPupper : VP ≤ L ^ (2 : ℕ)) (hQupper : VQ ≤ L ^ (2 : ℕ)) :
    (∑ c : CrudeWordCode R N R, c.badReciprocalCost VP VQ) ≤
      Real.exp ((9 + 7 * C) * s * (Real.log L) ^ 2) := by
  calc
    _ ≤ ∑ _c : CrudeWordCode R N R,
        Real.exp ((8 + 2 * C) * s * (Real.log L) ^ 2) := by
      exact sum_le_sum (fun c _ => short_badReciprocalCost_bound c VP VQ L C
        hs hL hlog hR hslots hN hspoly hP hQ hPupper hQupper)
    _ = (Fintype.card (CrudeWordCode R N R) : ℝ) *
        Real.exp ((8 + 2 * C) * s * (Real.log L) ^ 2) := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ Real.exp ((1 + 5 * C) * s * (Real.log L) ^ 2) *
        Real.exp ((8 + 2 * C) * s * (Real.log L) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (short_crudeWordCode_bound R N s L C hlog hR hslots hN hspoly)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The complete catalog, including both bounded integer parameters, has
the required `exp (O(s log² L))` reciprocal cost. -/
theorem badCatalogCost_exp_bound (s T : ℕ) (VP VQ L C : ℝ)
    (hs : 1 ≤ s) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hslots : (T : ℝ) ≤ C * s * Real.log L)
    (hT : (T : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hspoly : (s : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ)
    (hPupper : VP ≤ L ^ (2 : ℕ)) (hQupper : VQ ≤ L ^ (2 : ℕ)) :
    badCatalogCost s T VP VQ ≤
      Real.exp ((13 + 7 * C) * s * (Real.log L) ^ 2) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hfactor : ((s + 1) * (T + 1) : ℕ) ≤
      Real.exp ((4 : ℝ) * s * (Real.log L) ^ 2) := by
    calc
      _ = ((s : ℝ) + 1) * ((T : ℝ) + 1) := by push_cast; rfl
      _ ≤ L ^ (2 : ℕ) * L ^ (2 : ℕ) := by gcongr
      _ = L ^ (4 : ℕ) := by ring
      _ ≤ _ := short_polynomial_exp_bound s 4 L hs hLp hlog
  calc
    badCatalogCost s T VP VQ ≤ ∑ _R : Fin (s + 1), ∑ _N : Fin (T + 1),
        Real.exp ((9 + 7 * C) * s * (Real.log L) ^ 2) := by
      apply sum_le_sum
      intro R _
      apply sum_le_sum
      intro N _
      apply short_badCode_sum_bound R.val N.val s VP VQ L C hs hL hlog
        (Nat.le_of_lt_succ R.isLt) _ _ hspoly hP hQ hPupper hQupper
      · have hh : (N.val : ℝ) ≤ T := by exact_mod_cast Nat.le_of_lt_succ N.isLt
        exact hh.trans hslots
      · have hh : (N.val : ℝ) ≤ T := by exact_mod_cast Nat.le_of_lt_succ N.isLt
        linarith
    _ = (((s + 1) * (T + 1) : ℕ) : ℝ) *
        Real.exp ((9 + 7 * C) * s * (Real.log L) ^ 2) := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ Real.exp ((4 : ℝ) * s * (Real.log L) ^ 2) *
        Real.exp ((9 + 7 * C) * s * (Real.log L) ^ 2) :=
      mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

open Filter

/-- The polynomial side conditions in the finite estimate follow from the
actual short-word and slot budgets once the scale is sufficiently large. -/
theorem eventually_badCatalogCost_exp_bound (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (s T : ℕ) (VP VQ : ℝ),
      1 ≤ s → (s : ℝ) ≤ L ^ (1 / 10 : ℝ) →
      (T : ℝ) ≤ C * s * Real.log L →
      0 ≤ VP → 0 ≤ VQ → VP ≤ L ^ (2 : ℕ) → VQ ≤ L ^ (2 : ℕ) →
      badCatalogCost s T VP VQ ≤
        Real.exp ((13 + 7 * C) * s * (Real.log L) ^ 2) := by
  have hsmall := (isLittleO_log_rpow_atTop
    (show 0 < (9 / 10 : ℝ) by norm_num)).bound
      (show 0 < 1 / (C + 1) by positivity)
  filter_upwards [eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1), hsmall] with L hL hlog hh
  intro s T VP VQ hs hsupper hslots hP hQ hPupper hQupper
  have hLp : 0 < L := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ Real.log L by linarith),
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hh
  have hClog : C * Real.log L ≤ L ^ (9 / 10 : ℝ) := by
    calc
      _ ≤ (C + 1) * Real.log L := by nlinarith
      _ ≤ (C + 1) * ((1 / (C + 1)) * L ^ (9 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by field_simp [show C + 1 ≠ 0 by linarith]
  have hsL : (s : ℝ) ≤ L := by
    apply hsupper.trans
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (show 1 ≤ L by linarith)
        (show (1 / 10 : ℝ) ≤ 1 by norm_num)
  have hTL : (T : ℝ) ≤ L := by
    calc
      _ ≤ (s : ℝ) * (C * Real.log L) := by nlinarith [hslots]
      _ ≤ L ^ (1 / 10 : ℝ) * L ^ (9 / 10 : ℝ) :=
        mul_le_mul hsupper hClog (by positivity) (by positivity)
      _ = L := by rw [← Real.rpow_add hLp]; norm_num
  exact badCatalogCost_exp_bound s T VP VQ L C hs (by linarith) hlog hslots
    (by nlinarith) (by nlinarith) hP hQ hPupper hQupper

/-- The full short-word enumeration is dominated by the single prime
saving. This is the numerical end of the prohibited-site density estimate. -/
theorem eventually_badCatalog_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (s T : ℕ) (VP VQ H B total : ℝ),
      1 ≤ s → (s : ℝ) ≤ L ^ (1 / 10 : ℝ) →
      (T : ℝ) ≤ C * s * Real.log L →
      0 ≤ VP → 0 ≤ VQ → VP ≤ L ^ (2 : ℕ) → VQ ≤ L ^ (2 : ℕ) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H → 1 ≤ B → B ≤ Real.exp L →
      total ≤ badCatalogCost s T VP VQ * (H⁻¹ + (1 + Real.log B) / H) →
      total ≤ Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
  filter_upwards [eventually_badCatalogCost_exp_bound C hC,
    eventually_bad_event_decay (13 + 7 * C) (by positivity)] with L hcost hdecay
  intro s T VP VQ H B total hs hsupper hslots hP hQ hPupper hQupper hH hB hBupper htotal
  exact hdecay s H B (badCatalogCost s T VP VQ) total hsupper hH hB hBupper
    (hcost s T VP VQ hs hsupper hslots hP hQ hPupper hQupper) htotal

end TwoPointCorrelations

end OAI

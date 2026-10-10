import OAI.Combinatorics.EditApproximation.Coarse.CoarseProbability
import OAI.Combinatorics.EditApproximation.Numerics.NumericalWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Exact common precision of the coarse recurrence

Minima and threshold maxima select existing rationals. All computed arrays
therefore share one denominator whose bit length grows linearly with depth.
-/

namespace EditApproximation

open Finset

universe u

theorem coarse_rat_add_den_dvd (x y : ℚ) (common : ℕ)
    (hx : x.den ∣ common) (hy : y.den ∣ common) : (x + y).den ∣ common :=
  (Rat.add_den_dvd_lcm x y).trans (Nat.lcm_dvd hx hy)

theorem coarse_rat_mul_nat_den_dvd (x : ℚ) (n common : ℕ)
    (hx : x.den ∣ common) : (x * n).den ∣ common := by
  have h := Rat.mul_den_dvd x (n : ℚ)
  simp only [Rat.den_natCast, mul_one] at h
  exact h.trans hx

theorem coarse_rat_div_nat_den_dvd (x : ℚ) (n common : ℕ)
    (hn : 0 < n) (hx : x.den ∣ common) : (x / n).den ∣ common * n := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_eq_mul_inv]
  have h := Rat.mul_den_dvd x ((n : ℚ)⁻¹)
  simp only [Rat.den_inv_of_ne_zero hnq, Rat.num_natCast, Int.natAbs_natCast] at h
  exact h.trans (Nat.mul_dvd_mul hx (dvd_refl n))

theorem coarseThresholdContribution_den_dvd (threshold scale value : ℚ) (common : ℕ)
    (hscale : scale.den ∣ common) (hvalue : value.den ∣ common) :
    (coarseThresholdContribution threshold scale value).den ∣ common := by
  unfold coarseThresholdContribution
  split_ifs
  · rcases le_total value scale with h | h
    · simpa only [max_eq_right h] using hscale
    · simpa only [max_eq_left h] using hvalue
  · simp only [Rat.den_zero, one_dvd]

/-- A complete transformed child minimum retains the common precision. -/
theorem coarsePenaltyMinimum_den_dvd (k : ℕ) (value : Fin (2 * k + 1) → ℚ)
    (shift : Fin (2 * k + 1)) (common : ℕ) (hvalue : ∀ next, (value next).den ∣ common) :
    (univ.inf' univ_nonempty (fun next => value next + 2 * Nat.dist shift.val next.val)).den ∣ common := by
  obtain ⟨next, hnext, hminimum⟩ := exists_mem_eq_inf' (s := univ) univ_nonempty
    (fun next => value next + 2 * Nat.dist shift.val next.val)
  rw [hminimum]
  apply coarse_rat_add_den_dvd _ _ common (hvalue next)
  have hnat : (2 * (Nat.dist shift.val next.val : ℚ)).den = 1 := by
    exact_mod_cast (Rat.den_natCast (2 * Nat.dist shift.val next.val))
  simp only [hnat, one_dvd]

theorem coarseThresholdChildrenCost_den_dvd {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam allowance : ℚ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (common : ℕ) (hscale : (allowance / Q).den ∣ common)
    (hchild : ∀ child draw below, (child, draw, below) ∈ children → ∀ start shift,
      (value child below (lam * coarseChildThreshold B Q allowance draw) start shift).den ∣ common)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    (coarseThresholdChildrenCost k Q lam value allowance children start shift).den ∣ common := by
  induction children generalizing start with
  | nil => simp only [coarseThresholdChildrenCost, Rat.den_zero, one_dvd]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    simp only [coarseThresholdChildrenCost]
    apply coarse_rat_add_den_dvd _ _ common
    · apply coarseThresholdContribution_den_dvd _ _ _ common hscale
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        coarsePenaltyMinimum_den_dvd k _ shift common (hchild child draw below (by simp) start)
    · exact ih (fun child draw below hmem => hchild child draw below (by simp [hmem])) _



/-- The literal rational coarse estimator has a single common denominator,
including every pruning outcome and every choice of threshold labels. -/
theorem coarseThresholdEstimate_den_dvd {B D : ℕ} {α : Type u} [DecidableEq α]
    (k q L : ℕ) (frame : List (Option α)) (tree : CoarseSourceTree B α D)
    (draws : CoarseThresholdDraws B D) (allowance : ℚ) (allowanceDen : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (hden : 0 < allowanceDen)
    (hallowance : allowance.den ∣ allowanceDen) (start : ℕ) (shift : Fin (2 * k + 1)) :
    (coarseThresholdEstimate k q (1 / L) frame tree draws allowance start shift).den ∣
      coarseCommonDenominator allowanceDen q L B D := by
  induction tree generalizing allowance allowanceDen start shift with
  | leaf letter =>
    simp only [coarseThresholdEstimate]
    split_ifs
    · simp only [Rat.den_zero, one_dvd]
    · simp only [Rat.den_natCast, one_dvd]
  | @branch D children ih =>
    obtain ⟨draws, below⟩ := draws
    simp only [coarseThresholdEstimate]
    split_ifs
    · simp only [Rat.den_zero, one_dvd]
    · apply coarseThresholdChildrenCost_den_dvd
      · exact (coarse_rat_div_nat_den_dvd allowance q allowanceDen hq hallowance).trans
          (dvd_mul_right _ _)
      · intro child draw childBelow hmem childStart childShift
        obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
        cases hi
        have hthreshold : (coarseChildThreshold B q allowance (draws i)).den ∣ allowanceDen * (B * q) := by
          simpa only [coarseChildThreshold, Nat.cast_mul] using
            coarse_rat_div_nat_den_dvd (allowance * (draws i).val.succ) (B * q) allowanceDen
              (Nat.mul_pos hB hq) (coarse_rat_mul_nat_den_dvd allowance _ allowanceDen hallowance)
        have hchildDen : ((1 / (L : ℚ)) * coarseChildThreshold B q allowance (draws i)).den ∣
            allowanceDen * (L * B * q) := by
          have heq : (1 / (L : ℚ)) * coarseChildThreshold B q allowance (draws i) =
              coarseChildThreshold B q allowance (draws i) / L := by ring
          rw [heq]
          convert coarse_rat_div_nat_den_dvd _ L (allowanceDen * (B * q)) hL hthreshold using 1
          ring
        have hchild := ih i (below i) _ (allowanceDen * (L * B * q)) (by positivity) hchildDen
          childStart childShift
        convert hchild using 1
        simp only [coarseCommonDenominator, pow_succ]
        ring

/-- The common-denominator representation needs only linearly many
factor bit lengths per coarse depth. -/
theorem coarseCommonDenominator_bits (allowanceDen q L B D : ℕ) :
    Nat.size (coarseCommonDenominator allowanceDen q L B D) ≤
      Nat.size allowanceDen + Nat.size q + D * (Nat.size L + Nat.size B + Nat.size q) + 1 := by
  have hfirst := natural_product_bit_length allowanceDen q
  have hbase := natural_product_bit_length L B
  have hbaseSecond := natural_product_bit_length (L * B) q
  have hpower := natural_power_bit_length (L * B * q) D
  have htotal := natural_product_bit_length (allowanceDen * q) ((L * B * q) ^ D)
  unfold coarseCommonDenominator
  nlinarith

theorem coarseChildThreshold_le_scale {B : ℕ} (draw : Fin B)
    (Q allowance : ℚ) (hQ : 0 < Q) (ha : 0 ≤ allowance) :
    coarseChildThreshold B Q allowance draw ≤ allowance / Q := by
  have hB : (0 : ℚ) < B := by exact_mod_cast Nat.zero_lt_of_lt draw.isLt
  have hlabel : (draw.val + 1 : ℕ) ≤ B := by omega
  have hlabelQ : ((draw.val + 1 : ℕ) : ℚ) ≤ B := by exact_mod_cast hlabel
  unfold coarseChildThreshold
  apply (div_le_iff₀ (mul_pos hB hQ)).2
  calc
    _ ≤ allowance * B := mul_le_mul_of_nonneg_left hlabelQ ha
    _ = _ := by field_simp

theorem coarseChildAllowance_le {B : ℕ} (draw : Fin B)
    (Q lam allowance : ℚ) (hQ : 1 ≤ Q) (hlamone : lam ≤ 1)
    (ha : 0 ≤ allowance) : lam * coarseChildThreshold B Q allowance draw ≤ allowance := by
  have hthreshold := coarseChildThreshold_le_scale draw Q allowance (by linarith) ha
  have hthresholdNonneg := coarseChildThreshold_nonneg (Q := Q) (allowance := allowance) draw (by linarith) ha
  have hscale : allowance / Q ≤ allowance := (div_le_self ha hQ)
  exact (mul_le_of_le_one_left hthresholdNonneg hlamone).trans (hthreshold.trans hscale)

theorem coarseThresholdContribution_le_candidate (threshold scale value candidate : ℚ)
    (hscale : 0 ≤ scale) (hcandidate : 0 ≤ candidate) (hle : value ≤ candidate) :
    coarseThresholdContribution threshold scale value ≤ candidate + scale := by
  unfold coarseThresholdContribution
  split_ifs
  · exact max_le (by linarith) (by linarith)
  · exact add_nonneg hcandidate hscale

theorem coarseThresholdChildrenCost_le_width {B D : ℕ} {α : Type u}
    (k : ℕ) (Q lam allowance C : ℚ)
    (value : CoarseSourceTree B α D → CoarseThresholdDraws B D → ℚ → ℕ → Fin (2 * k + 1) → ℚ)
    (children : List (CoarseSourceTree B α D × Fin B × CoarseThresholdDraws B D))
    (hscale : 0 ≤ allowance / Q)
    (hchild : ∀ child draw below, (child, draw, below) ∈ children → ∀ start shift,
      0 ≤ value child below (lam * coarseChildThreshold B Q allowance draw) start shift ∧
      value child below (lam * coarseChildThreshold B Q allowance draw) start shift ≤ child.word.length + C)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseThresholdChildrenCost k Q lam value allowance children start shift ≤
      ((children.map (fun data => data.1.word)).flatten.length : ℚ) +
        children.length * (C + allowance / Q) := by
  induction children generalizing start with
  | nil => simp only [coarseThresholdChildrenCost, List.map_nil, List.flatten_nil, List.length_nil,
      Nat.cast_zero, zero_mul, zero_add, le_refl]
  | cons data rest ih =>
    obtain ⟨child, draw, below⟩ := data
    have hminimum := inf'_le
      (fun next => value child below (lam * coarseChildThreshold B Q allowance draw) start next +
        (2 * Nat.dist shift.val next.val : ℕ)) (mem_univ shift)
    simp only [Nat.dist_self, mul_zero, Nat.cast_zero, add_zero] at hminimum
    have hchildBound := hchild child draw below (by simp) start shift
    have hstep := (coarseThresholdContribution_le_candidate (coarseChildThreshold B Q allowance draw) _ _ _ hscale
      hchildBound.1 hminimum).trans (add_le_add hchildBound.2 le_rfl)
    have hrest := ih (fun child draw below hmem => hchild child draw below (by simp [hmem]))
      (start + child.word.length)
    simp only [coarseThresholdChildrenCost, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- All actual coarse estimates have polynomial magnitude, independently
of all accuracy events and all pruning outcomes. -/
theorem coarseThresholdEstimate_magnitude {B D : ℕ} {α : Type u} [DecidableEq α]
    (k : ℕ) (Q lam : ℚ) (frame : List (Option α))
    (tree : CoarseSourceTree B α D) (draws : CoarseThresholdDraws B D)
    (allowance : ℚ) (hQ : 1 ≤ Q) (hlam : 0 ≤ lam) (hlamone : lam ≤ 1)
    (ha : 0 ≤ allowance) (start : ℕ) (shift : Fin (2 * k + 1)) :
    coarseThresholdEstimate k Q lam frame tree draws allowance start shift ≤
      tree.word.length + B * allowance / Q * coarseInternalNodes B D := by
  have hQzero : 0 ≤ Q := by linarith
  induction tree generalizing allowance start shift with
  | leaf letter =>
    simp only [coarseThresholdEstimate]
    split_ifs
    · positivity
    · have hwidth := coarseShiftCost_le_width k frame (.leaf (B := B) letter) start shift
      simp only [coarseInternalNodes, Nat.cast_zero, mul_zero, add_zero]
      exact_mod_cast hwidth
  | @branch D children ih =>
    obtain ⟨draws, below⟩ := draws
    simp only [coarseThresholdEstimate]
    split_ifs
    · positivity
    · have hsum := coarseThresholdChildrenCost_le_width k Q lam allowance
        (B * allowance / Q * coarseInternalNodes B D)
        (fun child => coarseThresholdEstimate k Q lam frame child)
        (List.ofFn fun i => (children i, draws i, below i)) (div_nonneg ha (by linarith))
        (by
          intro child draw childBelow hmem childStart childShift
          obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
          cases hi
          have hchildAllowanceNonneg := mul_nonneg hlam (coarseChildThreshold_nonneg (Q := Q) (allowance := allowance) (draws i) (by linarith) ha)
          have hchildAllowance := coarseChildAllowance_le (draws i) Q lam allowance hQ hlamone ha
          have hbound := ih i (below i) _ hchildAllowanceNonneg childStart childShift
          have hprecision : (B : ℚ) * (lam * coarseChildThreshold B Q allowance (draws i)) / Q *
              coarseInternalNodes B D ≤ B * allowance / Q * coarseInternalNodes B D :=
            mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hchildAllowance
              (show (0 : ℚ) ≤ B by positivity))
              (show (0 : ℚ) ≤ Q by linarith))
            (show (0 : ℚ) ≤ coarseInternalNodes B D by positivity)
          exact ⟨coarseThresholdEstimate_nonneg k Q lam frame (children i) (below i) _
            childStart childShift (by linarith) hchildAllowanceNonneg,
            hbound.trans (add_le_add le_rfl hprecision)⟩)
        start shift
      convert hsum using 1
      simp only [List.length_ofFn, List.map_ofFn, Function.comp_def, CoarseSourceTree.word,
        coarseInternalNodes, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring

theorem coarse_rational_encoding_bits (value : ℚ) (M common : ℕ)
    (hcommon : 0 < common) (hden : value.den ∣ common) (hvalue : |value| ≤ M) :
    rationalEncodingBits value ≤ Nat.size M + 2 * Nat.size common + 1 := by
  have hnum := Nat.size_le_size (rational_numerator_bound value M hvalue)
  have hmul := natural_product_bit_length M value.den
  have hdenSize := Nat.size_le_size (Nat.le_of_dvd hcommon hden)
  unfold rationalEncodingBits
  omega

/-- Every root array cell actually produced at an integer allowance has
an explicit magnitude and denominator bit bound, regardless of accuracy. -/
theorem coarseThresholdEstimate_encoding_bits {B D : ℕ} {α : Type u} [DecidableEq α]
    (k q L : ℕ) (frame : List (Option α)) (tree : CoarseSourceTree B α D)
    (draws : CoarseThresholdDraws B D) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (start : ℕ) (shift : Fin (2 * k + 1)) :
    rationalEncodingBits (coarseThresholdEstimate k q (1 / L) frame tree draws k start shift) ≤
      Nat.size (tree.word.length + B * k * coarseInternalNodes B D) +
        2 * (Nat.size q + D * (Nat.size L + Nat.size B + Nat.size q) + 2) + 1 := by
  have hqQ : (1 : ℚ) ≤ q := by exact_mod_cast hq
  have hLQ : (1 : ℚ) ≤ L := by exact_mod_cast hL
  have hLpos : (0 : ℚ) < L := by exact_mod_cast hL
  have hlam : (0 : ℚ) ≤ 1 / L := by positivity
  have hlamOne : (1 : ℚ) / L ≤ 1 := (div_le_one hLpos).2 hLQ
  have hmagnitude := coarseThresholdEstimate_magnitude k q (1 / L) frame tree draws k hqQ
    hlam hlamOne (by positivity) start shift
  have hscaled : (B : ℚ) * k / q * coarseInternalNodes B D ≤ B * k * coarseInternalNodes B D :=
    mul_le_mul_of_nonneg_right (div_le_self (by positivity) hqQ) (by positivity)
  have habsolute : |coarseThresholdEstimate k q (1 / L) frame tree draws k start shift| ≤
      ((tree.word.length + B * k * coarseInternalNodes B D : ℕ) : ℚ) := by
    rw [abs_of_nonneg (coarseThresholdEstimate_nonneg k q (1 / L) frame tree draws k start shift
      (by positivity) (by positivity))]
    push_cast
    exact hmagnitude.trans (add_le_add le_rfl hscaled)
  have hden := coarseThresholdEstimate_den_dvd k q L frame tree draws k 1 hB hq hL (by decide)
    (by simp) start shift
  have hbits := coarse_rational_encoding_bits _
    (tree.word.length + B * k * coarseInternalNodes B D)
    (coarseCommonDenominator 1 q L B D) (by unfold coarseCommonDenominator; positivity) hden habsolute
  have hcommon := coarseCommonDenominator_bits 1 q L B D
  norm_num only [Nat.size_one] at hcommon
  omega

end EditApproximation

end OAI

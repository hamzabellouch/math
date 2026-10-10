import Mathlib
import OAI.Combinatorics.HoneycombBridges.LengthTransform

namespace OAI

/-! Exact-length renewal coefficients and bridge probabilities. -/

noncomputable section
open scoped ENNReal
open Filter

namespace HoneycombActual

def irreducibleListLength (bs : List IrreducibleBridge) : ℕ :=
  (bs.map (fun b => b.val.length)).sum

def irreducibleListWeight (bs : List IrreducibleBridge) : ℝ≥0∞ :=
  (bs.map (fun b => weight b.val)).prod

def exactPieceMass (n k : ℕ) : ℝ≥0∞ := by
  classical
  exact ∑' bs : {bs : List IrreducibleBridge // bs.length = k},
    if irreducibleListLength bs.val = n then irreducibleListWeight bs.val else 0

@[simp] theorem discountedWeight_zero (b : Bridge) : discountedWeight 0 0 b = weight b := by
  simp [discountedWeight]

theorem optionLength_irreducibleProduct_nat (bs : List IrreducibleBridge) :
    optionLength (irreducibleProduct bs) = irreducibleListLength bs := by
  simp [irreducibleProduct, optionLength_bridgeProduct, irreducibleListLength]

theorem optionWeight_irreducibleProduct_zero (bs : List IrreducibleBridge) :
    optionWeight 0 0 (irreducibleProduct bs) = irreducibleListWeight bs := by
  simpa [irreducibleListWeight] using optionWeight_irreducibleProduct 0 0 bs

theorem lengthMass_eq_listMass (n : ℕ) (hn : 0 < n) :
    criticalMass (fun b => b.length = n) = ∑' bs : List IrreducibleBridge,
      if irreducibleListLength bs = n then irreducibleListWeight bs else 0 := by
  classical
  let f : Option Bridge → ℝ≥0∞ := fun b =>
    if optionLength b = n then optionWeight 0 0 b else 0
  have hf : (∑' b : Option Bridge, f b) = criticalMass (fun b => b.length = n) := by
    rw [← (Equiv.optionEquivSumPUnit.{0,0} Bridge).symm.tsum_eq f,
      ENNReal.summable.tsum_sum ENNReal.summable]
    simp [f, optionLength, optionWeight, hn.ne, criticalMass, tsum_fintype]
    apply tsum_congr
    intro b
    by_cases hb : b.length = n <;> simp [hb]
  rw [← hf, ← irreducibleProductEquiv.tsum_eq f]
  apply tsum_congr
  intro bs
  change (if optionLength (irreducibleProduct bs) = n then
    optionWeight 0 0 (irreducibleProduct bs) else 0) = _
  rw [optionLength_irreducibleProduct_nat, optionWeight_irreducibleProduct_zero]

theorem lengthMass_eq_tsum_exactPieceMass (n : ℕ) (hn : 0 < n) :
    criticalMass (fun b => b.length = n) = ∑' k : ℕ, exactPieceMass n k := by
  classical
  rw [lengthMass_eq_listMass n hn,
    ← ENNReal.tsum_fiberwise (fun bs : List IrreducibleBridge =>
      if irreducibleListLength bs = n then irreducibleListWeight bs else 0) List.length]
  rfl

theorem exactPieceMass_zero_count (n : ℕ) (hn : 0 < n) : exactPieceMass n 0 = 0 := by
  classical
  apply ENNReal.tsum_eq_zero.mpr
  intro bs
  have he : bs.val = [] := List.length_eq_zero_iff.mp bs.property
  simp [he, irreducibleListLength, hn.ne]

theorem exactLengthRenewalIdentity (m : ℕ) (hm : 0 < m) :
    criticalMass (fun b => b.length = 2*m) =
      ∑' k : ℕ, exactPieceMass (2*m) (k+1) := by
  rw [lengthMass_eq_tsum_exactPieceMass (2*m) (by omega),
    tsum_eq_zero_add' ENNReal.summable,
    exactPieceMass_zero_count (2*m) (by omega), zero_add]

theorem two_mul_pieceCount_le_length (bs : List IrreducibleBridge) :
    2 * bs.length ≤ irreducibleListLength bs := by
  induction bs with
  | nil => simp [irreducibleListLength]
  | cons b bs ih =>
    have hpos := b.val.halfLength_pos
    have he := b.val.twice_halfLength
    simp only [List.length_cons, irreducibleListLength, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem exactPieceMass_eq_zero_of_halfLength_lt (m k : ℕ) (hk : m < k) :
    exactPieceMass (2*m) k = 0 := by
  classical
  apply ENNReal.tsum_eq_zero.mpr
  intro bs
  have h := two_mul_pieceCount_le_length bs.val
  have he : irreducibleListLength bs.val ≠ 2*m := by
    rw [bs.property] at h
    omega
  simp [he]

theorem exactLengthRenewalMass_pos_finite (m : ℕ) (hm : 0 < m) :
    0 < (∑' k : ℕ, exactPieceMass (2*m) (k+1)) ∧
    (∑' k : ℕ, exactPieceMass (2*m) (k+1)) < ⊤ := by
  rw [← exactLengthRenewalIdentity m hm]
  refine ⟨?_, (lengthMass_ne_top (2*m)).lt_top⟩
  exact (weight_pos (rowZigzag m hm)).trans_le
    (weight_le_criticalMass _ _ (rowZigzag_length m hm))



theorem uniformLengthProbability_mem_unitInterval (n : ℕ) (P : Bridge → Prop) :
    0 ≤ uniformLengthProbability n P ∧ uniformLengthProbability n P ≤ 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · let inclusion : {b : Bridge // b.length = n ∧ P b} →
        {b : Bridge // b.length = n} := fun b => ⟨b.val, b.property.1⟩
    have hi : Function.Injective inclusion := by
      intro b c he
      apply Subtype.ext
      exact congrArg (fun a : {b : Bridge // b.length = n} => a.val) he
    have hc := Nat.card_le_card_of_injective inclusion hi
    exact div_le_one_of_le₀ (by exact_mod_cast hc) (Nat.cast_nonneg _)

theorem uniformLengthProbability_univ (m : ℕ) (hm : 0 < m) :
    uniformLengthProbability (2*m) (fun _ => True) = 1 := by
  rw [uniformLengthProbability_eq_critical_ratio]
  simp only [and_true]
  have hp : 0 < criticalMass (fun b => b.length = 2*m) :=
    (weight_pos (rowZigzag m hm)).trans_le
      (weight_le_criticalMass _ _ (rowZigzag_length m hm))
  rw [ENNReal.div_self hp.ne' (lengthMass_ne_top (2*m))]
  norm_num

end HoneycombActual

end

end OAI

import OAI.Combinatorics.Ryser.Incidence.FiniteSets
import OAI.Combinatorics.Ryser.Incidence.ScalarCoverGeometry
import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [DecidableEq F]

private theorem scalar_card_image_le (c : F) (T : Finset F) :
    (c • T).card ≤ T.card := by
  change (T.image (fun x : F => c * x)).card ≤ T.card
  exact Finset.card_image_le

private theorem scalar_card_image_eq (c : F) (hc : c ≠ 0) (T : Finset F) :
    (c • T).card = T.card := by
  change (T.image (fun x : F => c * x)).card = T.card
  apply Finset.card_image_of_injective
  intro x y h
  exact mul_left_cancel₀ hc h

private theorem scalar_zero_image (T : Finset F) (hT : T.Nonempty) :
    (0 : F) • T = (0 : Finset F) := by
  change T.image (fun x : F => 0 * x) = ({0} : Finset F)
  simpa only [zero_mul] using Finset.image_const hT (0 : F)

private theorem scalar_one_image (T : Finset F) : (1 : F) • T = T := by
  change T.image (fun x : F => 1 * x) = T
  simp only [one_mul, Finset.image_id']

def ScalarCovered (B : Finset F) (K : ℝ) (c : F) (a : ℕ) : Prop :=
  ∃ T : Finset F, (T.card : ℝ) ≤ K ^ a ∧ c • B ⊆ T + (B - B)

private theorem scalar_card_add_le_bounds
    {T U : Finset F} {p q : ℝ}
    (hT : (T.card : ℝ) ≤ p) (hU : (U.card : ℝ) ≤ q) :
    ((T + U).card : ℝ) ≤ p * q := by
  have hcard : ((T + U).card : ℝ) ≤ (T.card : ℝ) * U.card := by
    exact_mod_cast (Finset.card_add_le (s := T) (t := U))
  exact hcard.trans (mul_le_mul hT hU (Nat.cast_nonneg _)
    ((Nat.cast_nonneg _).trans hT))

private theorem scalar_card_sub_le_bounds
    {T U : Finset F} {p q : ℝ}
    (hT : (T.card : ℝ) ≤ p) (hU : (U.card : ℝ) ≤ q) :
    ((T - U).card : ℝ) ≤ p * q := by
  have hcard : ((T - U).card : ℝ) ≤ (T.card : ℝ) * U.card := by
    exact_mod_cast (Finset.card_sub_le (s := T) (t := U))
  exact hcard.trans (mul_le_mul hT hU (Nat.cast_nonneg _)
    ((Nat.cast_nonneg _).trans hT))

variable {B E : Finset F} {K : ℝ} {c d : F} {a b : ℕ}

theorem scalarCovered_mono (hK : 1 ≤ K)
    (h : ScalarCovered B K c a) (hab : a ≤ b) :
    ScalarCovered B K c b := by
  rcases h with ⟨T, hT, hcover⟩
  exact ⟨T, hT.trans (pow_le_pow_right₀ hK hab), hcover⟩

theorem scalarCovered_of_sub_card (hB : B.Nonempty)
    (h : ((c • B - B).card : ℝ) ≤ K ^ a * B.card) :
    ScalarCovered B K c a := by
  obtain ⟨T, _, hT, hcover⟩ := covering_sub (c • B) B hB h
  exact ⟨T, hT, hcover⟩

theorem scalarCover_double_cover (hB : B.Nonempty)
    (hD : ((B - B).card : ℝ) ≤ K * B.card) :
    ∃ V : Finset F, (V.card : ℝ) ≤ K ^ 5 ∧
      (B - B) + (B - B) ⊆ V + (B - B) := by
  have heq : (B - B) + (B - B) - B =
      (2 : ℕ) • B - (3 : ℕ) • B := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, add_nsmul]
    simp only [two_nsmul, one_nsmul, sub_eq_add_neg, neg_add]
    ac_rfl
  have hsmall : (((B - B) + (B - B) - B).card : ℝ) ≤
      K ^ 5 * B.card := by
    rw [heq]
    simpa using multiple_sum_sub_card_le B hB hD 2 3
  obtain ⟨V, _, hV, hcover⟩ :=
    covering_sub ((B - B) + (B - B)) B hB hsmall
  exact ⟨V, hV, hcover⟩

private theorem scalarCover_difference_cost (hB : B.Nonempty)
    (hD : ((B - B).card : ℝ) ≤ K * B.card) :
    (((B - B) - B).card : ℝ) ≤ K ^ 3 * B.card := by
  simpa only [one_nsmul, two_nsmul, sub_eq_add_neg, neg_add, add_assoc]
    using multiple_sum_sub_card_le B hB hD 1 2

private theorem scalarCover_sum_cost (hB : B.Nonempty)
    (hD : ((B - B).card : ℝ) ≤ K * B.card) :
    ((B + (B - B)).card : ℝ) ≤ K ^ 3 * B.card := by
  simpa only [one_nsmul, two_nsmul, sub_eq_add_neg, add_assoc]
    using multiple_sum_sub_card_le B hB hD 2 1

theorem scalarCovered_seed (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hEB : ∀ e ∈ E, ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * B.card)
    (hc : c ∈ E ∨ c = 0 ∨ c = 1) :
    ScalarCovered B K c 4 := by
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 2).trans hK
  have hK1 : 1 ≤ K := one_le_two.trans hK
  rcases hc with hc | rfl | rfl
  · apply scalarCovered_of_sub_card hB
    have hswap : (c • B - B).card = (B - c • B).card := by
      simpa only [neg_sub] using Finset.card_neg (B - c • B)
    have hpow : 2 * K ^ 3 ≤ K ^ 4 := by
      calc
        2 * K ^ 3 ≤ K * K ^ 3 :=
          mul_le_mul_of_nonneg_right hK (pow_nonneg hK0 3)
        _ = K ^ 4 := by ring
    rw [hswap]
    exact (hEB c hc).trans
      (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  · have hzero : ScalarCovered B K (0 : F) 0 := by
      apply scalarCovered_of_sub_card hB
      simp only [scalar_zero_image B hB, zero_sub, Finset.card_neg,
        pow_zero, one_mul, le_refl]
    exact scalarCovered_mono hK1 hzero (by decide)
  · have hone : ScalarCovered B K (1 : F) 1 := by
      apply scalarCovered_of_sub_card hB
      simpa only [scalar_one_image, pow_one] using hD
    exact scalarCovered_mono hK1 hone (by decide)

theorem scalarCovered_neg (h : ScalarCovered B K c a) :
    ScalarCovered B K (-c) a := by
  rcases h with ⟨T, hT, hcover⟩
  refine ⟨-T, ?_, scalar_cover_neg_subset hcover⟩
  simpa only [Finset.card_neg] using hT

theorem scalarCovered_add (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) (hd : ScalarCovered B K d b) :
    ScalarCovered B K (c + d) (a + b + 5) := by
  let _ := hK
  rcases hc with ⟨T, hT, hTc⟩
  rcases hd with ⟨U, hU, hUd⟩
  obtain ⟨V, hV, hVcover⟩ := scalarCover_double_cover hB hD
  refine ⟨T + U + V, ?_, scalar_cover_add_subset hTc hUd hVcover⟩
  calc
    ((T + U + V).card : ℝ) ≤ (K ^ a * K ^ b) * K ^ 5 :=
      scalar_card_add_le_bounds (scalar_card_add_le_bounds hT hU) hV
    _ = K ^ (a + b + 5) := by simp only [pow_add]

theorem scalarCovered_sub (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) (hd : ScalarCovered B K d b) :
    ScalarCovered B K (c - d) (a + b + 5) := by
  let _ := hK
  rcases hc with ⟨T, hT, hTc⟩
  rcases hd with ⟨U, hU, hUd⟩
  obtain ⟨V, hV, hVcover⟩ := scalarCover_double_cover hB hD
  refine ⟨T - U + V, ?_, scalar_cover_sub_subset hTc hUd hVcover⟩
  calc
    ((T - U + V).card : ℝ) ≤ (K ^ a * K ^ b) * K ^ 5 :=
      scalar_card_add_le_bounds (scalar_card_sub_le_bounds hT hU) hV
    _ = K ^ (a + b + 5) := by simp only [pow_add]

theorem scalarCovered_mul (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) (hd : ScalarCovered B K d b) :
    ScalarCovered B K (c * d) (b + 2 * a + 5) := by
  let _ := hK
  rcases hc with ⟨T, hT, hTc⟩
  rcases hd with ⟨U, hU, hUd⟩
  obtain ⟨V, hV, hVcover⟩ := scalarCover_double_cover hB hD
  have hCU : ((c • U).card : ℝ) ≤ K ^ b :=
    (Nat.cast_le.mpr (scalar_card_image_le c U)).trans hU
  refine ⟨c • U + T - T + V, ?_,
    scalar_cover_mul_subset hTc hUd hVcover⟩
  calc
    ((c • U + T - T + V).card : ℝ) ≤
        ((K ^ b * K ^ a) * K ^ a) * K ^ 5 :=
      scalar_card_add_le_bounds
        (scalar_card_sub_le_bounds (scalar_card_add_le_bounds hCU hT) hT) hV
    _ = K ^ (b + 2 * a + 5) := by
      simp only [two_mul, pow_add]
      ring

theorem scalarCovered_card_sub (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) :
    ((c • B - B).card : ℝ) ≤ K ^ (a + 3) * B.card := by
  let _ := hK
  rcases hc with ⟨T, hT, hcover⟩
  have hsub : c • B - B ⊆ T + ((B - B) - B) := by
    simpa only [add_sub_assoc] using Finset.sub_subset_sub_right hcover
  calc
    ((c • B - B).card : ℝ) ≤ ((T + ((B - B) - B)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ K ^ a * (K ^ 3 * B.card) :=
      scalar_card_add_le_bounds hT (scalarCover_difference_cost hB hD)
    _ = K ^ (a + 3) * B.card := by rw [pow_add]; ring

theorem scalarCovered_inv (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) (hc0 : c ≠ 0) :
    ScalarCovered B K c⁻¹ (a + 3) := by
  have hcard : (c⁻¹ • B - B).card = (c • B - B).card := by
    rw [← scalar_cover_inv_sub_identity B hc0]
    exact scalar_card_image_eq (-c⁻¹) (neg_ne_zero.mpr (inv_ne_zero hc0)) _
  apply scalarCovered_of_sub_card hB
  rw [hcard]
  exact scalarCovered_card_sub hB hK hD hc

theorem scalarCovered_card_add (hB : B.Nonempty) (hK : 2 ≤ K)
    (hD : ((B - B).card : ℝ) ≤ K * B.card)
    (hc : ScalarCovered B K c a) :
    ((B + c • B).card : ℝ) ≤ K ^ (a + 3) * B.card := by
  let _ := hK
  rcases hc with ⟨T, hT, hcover⟩
  have hsub : B + c • B ⊆ T + (B + (B - B)) := by
    calc
      B + c • B ⊆ B + (T + (B - B)) :=
        Finset.add_subset_add_left hcover
      _ = T + (B + (B - B)) := by ac_rfl
  calc
    ((B + c • B).card : ℝ) ≤ ((T + (B + (B - B))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ K ^ a * (K ^ 3 * B.card) :=
      scalar_card_add_le_bounds hT (scalarCover_sum_cost hB hD)
    _ = K ^ (a + 3) * B.card := by rw [pow_add]; ring

end RyserCoveringCounterexample.Incidence

end

end OAI

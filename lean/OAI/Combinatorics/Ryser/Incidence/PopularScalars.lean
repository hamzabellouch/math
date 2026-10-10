import OAI.Combinatorics.Ryser.Incidence.FiniteSets
import OAI.Combinatorics.Ryser.Incidence.PopularOverlap
import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

open scoped Pointwise

namespace RyserCoveringCounterexample.Incidence

variable {F : Type*} [Field F] [DecidableEq F]

private theorem card_field_smul (c : F) (hc : c ≠ 0) (X : Finset F) :
    (c • X).card = X.card := by
  change (X.image (fun x : F => c * x)).card = X.card
  apply Finset.card_image_of_injective
  intro x y h
  exact mul_left_cancel₀ hc h

private theorem field_smul_smul (c d : F) (X : Finset F) :
    c • (d • X) = (c * d) • X := by
  change (X.image (fun x : F => d * x)).image (fun y : F => c * y) =
    X.image (fun x : F => (c * d) * x)
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x hx
  exact (mul_assoc c d x).symm

private theorem field_one_smul (X : Finset F) : (1 : F) • X = X := by
  change X.image (fun x : F => 1 * x) = X
  simp only [one_mul, Finset.image_id']

private theorem field_smul_sub (c : F) (X Y : Finset F) :
    c • (X - Y) = c • X - c • Y := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_smul_finset.mp hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hw
    change c * (x - y) ∈ c • X - c • Y
    rw [mul_sub]
    exact Finset.sub_mem_sub (Finset.smul_mem_smul_finset hx)
      (Finset.smul_mem_smul_finset hy)
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_smul_finset.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_smul_finset.mp hy
    refine Finset.mem_smul_finset.mpr ⟨u - v, Finset.sub_mem_sub hu hv, ?_⟩
    change c * (u - v) = c * u - c * v
    exact mul_sub c u v

private theorem field_smul_inter (c : F) (hc : c ≠ 0) (X Y : Finset F) :
    c • (X ∩ Y) = c • X ∩ c • Y := by
  change (X ∩ Y).image (fun x : F => c * x) =
    X.image (fun x : F => c * x) ∩ Y.image (fun x : F => c * x)
  apply Finset.image_inter
  intro x y h
  exact mul_left_cancel₀ hc h

private theorem quotient_overlap_card (S : Finset F) (a b : F) (ha : a ≠ 0) :
    ((a⁻¹ • S) ∩ (b⁻¹ • S)).card = (S ∩ (b⁻¹ * a) • S).card := by
  calc
    ((a⁻¹ • S) ∩ (b⁻¹ • S)).card =
        (a • ((a⁻¹ • S) ∩ (b⁻¹ • S))).card :=
      (card_field_smul a ha _).symm
    _ = (S ∩ (b⁻¹ * a) • S).card := by
      rw [field_smul_inter a ha, field_smul_smul, field_smul_smul,
        mul_inv_cancel₀ ha, field_one_smul, mul_comm a b⁻¹]

private theorem popular_difference_bound (S : Finset F) (c : F) (hc : c ≠ 0)
    (K : ℝ) (hS : S.Nonempty) (hK : 0 < K)
    (hsub : ((S - S).card : ℝ) ≤ K * S.card)
    (hoverlap : (S.card : ℝ) / (2 * K) ≤ (S ∩ c • S).card) :
    ((S - c • S).card : ℝ) ≤ 2 * K ^ 3 * S.card := by
  let Z := S ∩ c • S
  have hspos : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hleftNat : (S - Z).card ≤ (S - S).card :=
    Finset.card_le_card (Finset.sub_subset_sub (fun _ h => h) Finset.inter_subset_left)
  have hrightNat : (Z - c • S).card ≤ (c • S - c • S).card :=
    Finset.card_le_card (Finset.sub_subset_sub Finset.inter_subset_right (fun _ h => h))
  rw [← field_smul_sub c S S, card_field_smul c hc (S - S)] at hrightNat
  have hleft : ((S - Z).card : ℝ) ≤ K * S.card :=
    (show ((S - Z).card : ℝ) ≤ (S - S).card by exact_mod_cast hleftNat).trans hsub
  have hright : ((Z - c • S).card : ℝ) ≤ K * S.card :=
    (show ((Z - c • S).card : ℝ) ≤ (S - S).card by exact_mod_cast hrightNat).trans hsub
  have htriangle : ((S - c • S).card : ℝ) * Z.card ≤
      ((S - Z).card : ℝ) * (Z - c • S).card := by
    exact_mod_cast triangle_card_le S (c • S) Z
  have hproduct : ((S - c • S).card : ℝ) * Z.card ≤
      (K * S.card) * (K * S.card) :=
    htriangle.trans (mul_le_mul hleft hright (Nat.cast_nonneg _)
      (mul_nonneg hK.le (Nat.cast_nonneg _)))
  have hpopular : (S.card : ℝ) ≤ (Z.card : ℝ) * (2 * K) :=
    (div_le_iff₀ (by positivity : 0 < 2 * K)).mp hoverlap
  have hfinal : ((S - c • S).card : ℝ) * S.card ≤
      (2 * K ^ 3 * S.card) * S.card := calc
    ((S - c • S).card : ℝ) * S.card ≤
        ((S - c • S).card : ℝ) * ((Z.card : ℝ) * (2 * K)) :=
      mul_le_mul_of_nonneg_left hpopular (Nat.cast_nonneg _)
    _ = (2 * K) * (((S - c • S).card : ℝ) * Z.card) := by ring
    _ ≤ (2 * K) * ((K * S.card) * (K * S.card)) :=
      mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ = (2 * K ^ 3 * S.card) * S.card := by ring
  exact le_of_mul_le_mul_right hfinal hspos

theorem exists_popular_scalars (S : Finset F) (K : ℝ) (hS : S.Nonempty)
    (hzero : (0 : F) ∉ S) (hK : 2 ≤ K)
    (hsub : ((S - S).card : ℝ) ≤ K * S.card)
    (hdiv : ((S / S).card : ℝ) ≤ K * S.card) :
    ∃ B E : Finset F, E ⊆ B ∧ B.card = S.card ∧
      (S.card : ℝ) / (2 * K) ≤ E.card ∧
      ((B - B).card : ℝ) ≤ K * B.card ∧
      ∀ e ∈ E, ((B - e • B).card : ℝ) ≤ 2 * K ^ 3 * B.card := by
  classical
  have hnonzero : ∀ a ∈ S, a ≠ (0 : F) := by
    rintro a ha rfl
    exact hzero ha
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hquotient : ∀ a ∈ S, a⁻¹ • S ⊆ S / S := by
    intro a ha z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp hz
    refine Finset.mem_div.mpr ⟨x, hx, a, ha, ?_⟩
    change x / a = a⁻¹ * x
    rw [div_eq_mul_inv, mul_comm]
  obtain ⟨b, hb, A, hAS, hAcard, hpopular⟩ :=
    exists_popular_intersections S (fun a : F => a⁻¹ • S) (S / S) S.card K
      rfl hS (fun a ha => card_field_smul a⁻¹ (inv_ne_zero (hnonzero a ha)) S)
      hquotient hdiv hK
  have hb0 : b ≠ 0 := hnonzero b hb
  have hBcard : (b⁻¹ • S).card = S.card :=
    card_field_smul b⁻¹ (inv_ne_zero hb0) S
  have hEcard : (b⁻¹ • A).card = A.card :=
    card_field_smul b⁻¹ (inv_ne_zero hb0) A
  refine ⟨b⁻¹ • S, b⁻¹ • A, Finset.smul_finset_subset_smul_finset hAS,
    hBcard, ?_, ?_, ?_⟩
  · simpa only [hEcard] using hAcard
  · rw [← field_smul_sub b⁻¹ S S,
      card_field_smul b⁻¹ (inv_ne_zero hb0) (S - S), hBcard]
    exact hsub
  · intro e he
    obtain ⟨a, ha, hae⟩ := Finset.mem_smul_finset.mp he
    change b⁻¹ * a = e at hae
    subst e
    have ha0 : a ≠ 0 := hnonzero a (hAS ha)
    have he0 : b⁻¹ * a ≠ 0 := mul_ne_zero (inv_ne_zero hb0) ha0
    have hoverlap : (S.card : ℝ) / (2 * K) ≤ (S ∩ (b⁻¹ * a) • S).card := by
      rw [← quotient_overlap_card S a b ha0]
      exact hpopular a ha
    have hbound := popular_difference_bound S (b⁻¹ * a) he0 K hS hKpos hsub hoverlap
    have hscale : b⁻¹ • S - (b⁻¹ * a) • (b⁻¹ • S) =
        b⁻¹ • (S - (b⁻¹ * a) • S) := by
      rw [field_smul_sub]
      congr 1
      rw [field_smul_smul, field_smul_smul, mul_comm (b⁻¹ * a) b⁻¹]
    rw [hscale, card_field_smul b⁻¹ (inv_ne_zero hb0) (S - (b⁻¹ * a) • S), hBcard]
    exact hbound

end RyserCoveringCounterexample.Incidence

end OAI

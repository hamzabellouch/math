import Mathlib

namespace OAI


noncomputable section

namespace Problem355.Auxiliary

open Finset

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def badShifts (M S : Finset F) : Finset F :=
  M.biUnion fun m => S.image fun x => m⁻¹ * x

def allowedShifts (M S : Finset F) : Finset F :=
  univ \ badShifts M S

omit [Fintype F] in
lemma mem_badShifts_iff (M S : Finset F)
    (hM : ∀ m ∈ M, m ≠ 0) (a : F) :
    a ∈ badShifts M S ↔ ∃ m ∈ M, m * a ∈ S := by
  simp only [badShifts, mem_biUnion, mem_image]
  constructor
  · rintro ⟨m, hm, x, hx, rfl⟩
    exact ⟨m, hm, by simpa only [mul_inv_cancel_left₀ (hM m hm)] using hx⟩
  · rintro ⟨m, hm, hma⟩
    exact ⟨m, hm, m * a, hma, inv_mul_cancel_left₀ (hM m hm) a⟩

lemma mem_allowedShifts_iff (M S : Finset F)
    (hM : ∀ m ∈ M, m ≠ 0) (a : F) :
    a ∈ allowedShifts M S ↔ ∀ m ∈ M, m * a ∉ S := by
  simp [allowedShifts, mem_badShifts_iff M S hM a]

omit [Fintype F] in
lemma card_badShifts_le (M S : Finset F) :
    (badShifts M S).card ≤ M.card * S.card := by
  exact card_biUnion_le_card_mul M _ S.card fun _ _ => card_image_le

lemma card_le_allowedShifts_add (M S : Finset F) :
    Fintype.card F ≤ (allowedShifts M S).card + M.card * S.card := by
  have h := card_sdiff_add_card_eq_card (subset_univ (badShifts M S))
  rw [card_univ] at h
  calc
    Fintype.card F = (allowedShifts M S).card + (badShifts M S).card := h.symm
    _ ≤ _ := Nat.add_le_add_left (card_badShifts_le M S) _

end FiniteField

def integerWindow (q R : ℕ) : Finset (ZMod q) := by
  classical
  exact (Icc (-(R : ℤ)) (R : ℤ)).image fun z : ℤ => (z : ZMod q)

lemma card_integerWindow_le (q R : ℕ) :
    (integerWindow q R).card ≤ 2 * R + 1 := by
  classical
  calc
    (integerWindow q R).card ≤ (Icc (-(R : ℤ)) (R : ℤ)).card := by
      unfold integerWindow
      exact card_image_le
    _ = 2 * R + 1 := by rw [Int.card_Icc]; omega

lemma intCast_mem_integerWindow (q R : ℕ) (z : ℤ)
    (hz : |z| ≤ (R : ℤ)) : (z : ZMod q) ∈ integerWindow q R := by
  classical
  unfold integerWindow
  apply mem_image.mpr
  exact ⟨z, mem_Icc.mpr (abs_le.mp hz), rfl⟩

def positiveMultipliers (q H : ℕ) : Finset (ZMod q) := by
  classical
  exact (Icc 1 (3 * H)).image fun m : ℕ => (m : ZMod q)

lemma card_positiveMultipliers_le (q H : ℕ) :
    (positiveMultipliers q H).card ≤ 3 * H := by
  classical
  calc
    (positiveMultipliers q H).card ≤ (Icc 1 (3 * H)).card := by
      unfold positiveMultipliers
      exact card_image_le
    _ = 3 * H := by simp

lemma positiveMultipliers_ne_zero (q H : ℕ) (hq : 3 * H < q) :
    ∀ m ∈ positiveMultipliers q H, m ≠ 0 := by
  classical
  intro m hm
  unfold positiveMultipliers at hm
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
  intro hz
  exact Nat.not_dvd_of_pos_of_lt (mem_Icc.mp hn).1
    (lt_of_le_of_lt (mem_Icc.mp hn).2 hq) ((ZMod.natCast_eq_zero_iff n q).mp hz)

lemma card_allowed_auxiliary_shifts (q H w : ℕ) [Fact q.Prime] :
    q ≤ (allowedShifts (positiveMultipliers q H) (integerWindow q (3 * H * w))).card +
      3 * H * (6 * H * w + 1) := by
  classical
  have h := card_le_allowedShifts_add (positiveMultipliers q H)
    (integerWindow q (3 * H * w))
  rw [ZMod.card] at h
  refine h.trans (Nat.add_le_add_left ?_ _)
  calc
    (positiveMultipliers q H).card * (integerWindow q (3 * H * w)).card
        ≤ (3 * H) * (2 * (3 * H * w) + 1) :=
      Nat.mul_le_mul (card_positiveMultipliers_le q H)
        (card_integerWindow_le q (3 * H * w))
    _ = _ := by ring

lemma auxiliary_bad_count_lt_half (q H w : ℕ) (hH : 1 ≤ H)
    (hq : 2000 * H ^ 2 ≤ q) (hw : 1000 * H ^ 2 * w ≤ q) :
    2 * (3 * H * (6 * H * w + 1)) < q := by
  have hsq : H ≤ H ^ 2 := by nlinarith
  have hprod : 0 ≤ H ^ 2 * w := Nat.zero_le _
  nlinarith

lemma auxiliary_multiplier_range (q H : ℕ) (hH : 1 ≤ H)
    (hq : 2000 * H ^ 2 ≤ q) : 3 * H < q := by
  have hsq : H ≤ H ^ 2 := by nlinarith
  nlinarith

lemma auxiliary_allowed_card_gt_half (q H w : ℕ) [Fact q.Prime]
    (hH : 1 ≤ H) (hq : 2000 * H ^ 2 ≤ q)
    (hw : 1000 * H ^ 2 * w ≤ q) :
    q < 2 * (allowedShifts (positiveMultipliers q H)
      (integerWindow q (3 * H * w))).card := by
  have hc := card_allowed_auxiliary_shifts q H w
  have hb := auxiliary_bad_count_lt_half q H w hH hq hw
  omega

lemma exists_auxiliary_allowed_shift (q H w : ℕ) [Fact q.Prime]
    (hH : 1 ≤ H) (hq : 2000 * H ^ 2 ≤ q)
    (hw : 1000 * H ^ 2 * w ≤ q) :
    ∃ a : ZMod q, ∀ m : ℕ, 1 ≤ m → m ≤ 3 * H →
      (m : ZMod q) * a ∉ integerWindow q (3 * H * w) := by
  classical
  have hc := auxiliary_allowed_card_gt_half q H w hH hq hw
  have hp : 0 < (allowedShifts (positiveMultipliers q H)
      (integerWindow q (3 * H * w))).card := by omega
  obtain ⟨a, ha⟩ := card_pos.mp hp
  refine ⟨a, ?_⟩
  have ha' := (mem_allowedShifts_iff _ _
    (positiveMultipliers_ne_zero q H (auxiliary_multiplier_range q H hH hq)) a).mp ha
  intro m hm1 hmH
  apply ha'
  unfold positiveMultipliers
  exact mem_image.mpr ⟨m, mem_Icc.mpr ⟨hm1, hmH⟩, rfl⟩

lemma neg_mem_integerWindow {q R : ℕ} {a : ZMod q}
    (ha : a ∈ integerWindow q R) : -a ∈ integerWindow q R := by
  classical
  unfold integerWindow at *
  obtain ⟨z, hz, rfl⟩ := mem_image.mp ha
  refine mem_image.mpr ⟨-z, ?_, by simp⟩
  apply mem_Icc.mpr
  have hz' := abs_le.mpr (mem_Icc.mp hz)
  exact abs_le.mp (by simpa only [abs_neg] using hz')

lemma int_mul_not_mem_integerWindow (q H R : ℕ) (a : ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a ∉ integerWindow q R)
    (m : ℤ) (hm0 : m ≠ 0) (hm : |m| ≤ (3 * H : ℕ)) :
    (m : ZMod q) * a ∉ integerWindow q R := by
  have hn0 : 1 ≤ m.natAbs := Int.natAbs_pos.mpr hm0
  have hnH : m.natAbs ≤ 3 * H := by
    have h : (m.natAbs : ℤ) ≤ (3 * H : ℕ) := by
      simpa only [Int.natCast_natAbs] using hm
    exact_mod_cast h
  have hne := ha m.natAbs hn0 hnH
  by_cases hnonneg : 0 ≤ m
  · have heq : (m.natAbs : ZMod q) = (m : ZMod q) := by
      have h := congrArg (fun z : ℤ => (z : ZMod q)) (Int.natAbs_of_nonneg hnonneg)
      simpa using h
    simpa only [heq] using hne
  · have heq : (m.natAbs : ZMod q) = -(m : ZMod q) := by
      have h : (m.natAbs : ℤ) = -m := by
        rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hnonneg)]
      have h' := congrArg (fun z : ℤ => (z : ZMod q)) h
      simpa using h'
    intro hmem
    apply hne
    rw [heq, neg_mul]
    exact neg_mem_integerWindow hmem

lemma abs_sum_three_le (f : Fin 3 → ℤ) (B : ℤ)
    (hf : ∀ i, |f i| ≤ B) : |∑ i, f i| ≤ 3 * B := by
  calc
    |∑ i, f i| ≤ ∑ i, |f i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, B := sum_le_sum fun i _ => hf i
    _ = 3 * B := by simp

lemma shifted_scalar_short_relation_ne_zero (q H w : ℕ) (a : ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a ∉ integerWindow q (3 * H * w))
    (x v : Fin 3 → ℤ) (hx : ∀ i, |x i| ≤ (H : ℤ))
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ (w : ℤ))
    (hsum : ∑ i, x i ≠ 0) :
    (∑ i, (x i : ZMod q) * (a + (v i : ZMod q))) ≠ 0 := by
  intro hrel
  have hm : |∑ i, x i| ≤ (3 * H : ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using abs_sum_three_le x (H : ℤ) hx
  have hforbid := int_mul_not_mem_integerWindow q H (3 * H * w) a ha
    (∑ i, x i) hsum hm
  have hb : |∑ i, x i * v i| ≤ (3 * H * w : ℕ) := by
    have hb' := abs_sum_three_le (fun i => x i * v i) ((H : ℤ) * w) (by
      intro i
      rw [abs_mul, abs_of_nonneg (hv i).1]
      exact mul_le_mul (hx i) (hv i).2 (hv i).1 (by positivity))
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hb'
  have heq : ((∑ i, x i : ℤ) : ZMod q) * a =
      ((-(∑ i, x i * v i) : ℤ) : ZMod q) := by
    push_cast
    rw [eq_neg_iff_add_eq_zero]
    simpa only [sum_mul, mul_add, sum_add_distrib] using hrel
  apply hforbid
  rw [heq]
  apply intCast_mem_integerWindow
  simpa only [abs_neg] using hb

lemma exists_auxiliary_allowed_shift_div (q H : ℕ) [Fact q.Prime]
    (hH : 1 ≤ H) (hq : 2000 * H ^ 2 ≤ q) :
    ∃ a : ZMod q, ∀ m : ℕ, 1 ≤ m → m ≤ 3 * H →
      (m : ZMod q) * a ∉
        integerWindow q (3 * H * (q / (1000 * H ^ 2))) := by
  exact exists_auxiliary_allowed_shift q H _ hH hq (Nat.mul_div_le _ _)

lemma shifted_vector_short_relation_ne_zero (q H w : ℕ)
    (a : Fin 3 → ZMod q)
    (ha : ∀ n : ℕ, 1 ≤ n → n ≤ 3 * H →
      (n : ZMod q) * a 0 ∉ integerWindow q (3 * H * w))
    (x : Fin 3 → ℤ) (v : Fin 3 → Fin 3 → ℤ)
    (hx : ∀ i, |x i| ≤ (H : ℤ))
    (hv : ∀ i, 0 ≤ v i 0 ∧ v i 0 ≤ (w : ℤ))
    (hsum : ∑ i, x i ≠ 0)
    (G : (Fin 3 → ZMod q) ≃ₗ[ZMod q] (Fin 3 → ZMod q)) :
    (∑ i, (x i : ZMod q) • G (a + fun j => (v i j : ZMod q))) ≠ 0 := by
  intro hrel
  have hrel' : (∑ i, (x i : ZMod q) • (a + fun j => (v i j : ZMod q))) = 0 := by
    apply G.injective
    simpa only [map_sum, map_smul, map_zero] using hrel
  have hzero := congrFun hrel' 0
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul] at hzero
  exact shifted_scalar_short_relation_ne_zero q H w (a 0) ha x (fun i => v i 0)
    hx hv hsum hzero

section VectorShifts

variable {F : Type*} [Fintype F] [DecidableEq F]

def vectorShifts (S : Finset F) : Finset (Fin 3 → F) :=
  (S.product (univ.product univ)).image fun p : F × F × F => ![p.1, p.2.1, p.2.2]

lemma mem_vectorShifts_iff (S : Finset F) (a : Fin 3 → F) :
    a ∈ vectorShifts S ↔ a 0 ∈ S := by
  unfold vectorShifts
  constructor
  · rintro h
    obtain ⟨⟨x, y, z⟩, hxyz, rfl⟩ := mem_image.mp h
    exact (mem_product.mp hxyz).1
  · intro ha
    refine mem_image.mpr ⟨(a 0, a 1, a 2), by simp [ha], ?_⟩
    funext i
    fin_cases i <;> rfl

lemma card_vectorShifts (S : Finset F) :
    (vectorShifts S).card = S.card * Fintype.card F ^ 2 := by
  unfold vectorShifts
  rw [card_image_of_injective]
  · simp [pow_two]
  · intro p r h
    apply Prod.ext
    · simpa using congrFun h (0 : Fin 3)
    · apply Prod.ext
      · simpa using congrFun h (1 : Fin 3)
      · simpa using congrFun h (2 : Fin 3)

end VectorShifts

lemma auxiliary_allowed_vector_card_gt_half (q H w : ℕ) [Fact q.Prime]
    (hH : 1 ≤ H) (hq : 2000 * H ^ 2 ≤ q)
    (hw : 1000 * H ^ 2 * w ≤ q) :
    q ^ 3 < 2 * (vectorShifts (allowedShifts (positiveMultipliers q H)
      (integerWindow q (3 * H * w)))).card := by
  rw [card_vectorShifts, ZMod.card]
  have hc := auxiliary_allowed_card_gt_half q H w hH hq hw
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  have h := Nat.mul_lt_mul_of_pos_right hc (pow_pos hqpos 2)
  nlinarith

end Problem355.Auxiliary

end

end OAI

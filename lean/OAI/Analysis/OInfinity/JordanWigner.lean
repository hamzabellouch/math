import OAI.Analysis.OInfinity.EvenModeCAR

namespace OAI

/-! # Finite Jordan–Wigner coordinates in a CAR corner

The occupation parities and their finite prefix products turn the given CAR
modes into commuting two-level coordinates. All products below are finite;
no representation or completion of an infinite CAR algebra is used.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Twice the occupation projection is subtracted from the corner unit. -/
def carModeParity (q a : E) : E := q - (star a * a + star a * a)

lemma carModeParity_properties (q a : E) (hqstar : star q = q) (hqq : q * q = q)
    (hqa : q * a = a) (haq : a * q = a) (haa : a * a = 0)
    (hgram : star a * a + a * star a = q) :
    star (carModeParity q a) = carModeParity q a ∧
      carModeParity q a * carModeParity q a = q ∧
      q * carModeParity q a = carModeParity q a ∧
      carModeParity q a * q = carModeParity q a ∧
      carModeParity q a * a = a ∧ a * carModeParity q a = -a := by
  have hqa' : q * star a = star a := by
    simpa only [star_mul, hqstar] using congrArg star haq
  have han : a * (star a * a) = a := by
    calc
      _ = (a * star a) * a := by noncomm_ring
      _ = (q - star a * a) * a := by rw [← hgram]; noncomm_ring
      _ = a := by rw [sub_mul, hqa, mul_assoc, haa, mul_zero, sub_zero]
  have hna : (star a * a) * a = 0 := by rw [mul_assoc, haa, mul_zero]
  have hqn : q * (star a * a) = star a * a := by rw [← mul_assoc, hqa']
  have hnq : (star a * a) * q = star a * a := by rw [mul_assoc, haq]
  have hnn : (star a * a) * (star a * a) = star a * a := by rw [mul_assoc, han]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [carModeParity, star_sub, star_add, star_mul, star_star, hqstar]
  · simp only [carModeParity, sub_mul, mul_sub, add_mul, mul_add,
      hqq, hqn, hnq, hnn]
    abel
  · simp only [carModeParity, mul_sub, mul_add, hqq, hqn]
  · simp only [carModeParity, sub_mul, add_mul, hqq, hnq]
  · simp only [carModeParity, sub_mul, add_mul, hqa, hna, zero_add, sub_zero]
  · simp only [carModeParity, mul_sub, mul_add, haq, han]
    abel

lemma carOccupation_commute (a b : E) (hab : a * b + b * a = 0)
    (hstar : star a * b + b * star a = 0) : Commute (star a * a) b := by
  have hab' : a * b = -(b * a) := eq_neg_of_add_eq_zero_left hab
  have hstar' : star a * b = -(b * star a) := eq_neg_of_add_eq_zero_left hstar
  change (star a * a) * b = b * (star a * a)
  calc
    _ = star a * (a * b) := by noncomm_ring
    _ = -(star a * b) * a := by rw [hab']; noncomm_ring
    _ = b * (star a * a) := by rw [hstar']; noncomm_ring

lemma carModeParity_commute (q a b : E) (hqb : q * b = b) (hbq : b * q = b)
    (hab : a * b + b * a = 0) (hstar : star a * b + b * star a = 0) :
    Commute (carModeParity q a) b := by
  have hq : Commute q b := by change q * b = b * q; rw [hqb, hbq]
  have hn := carOccupation_commute a b hab hstar
  exact hq.sub_left (hn.add_left hn)

def carParityPrefix (q : E) (c : ℕ → E) : ℕ → E
  | 0 => q
  | k + 1 => carParityPrefix q c k * carModeParity q (c k)

def carJordanWigner (q : E) (c : ℕ → E) (k : ℕ) : E := carParityPrefix q c k * c k

section Family

variable (q : E) (c : ℕ → E) (hqstar : star q = q) (hqq : q * q = q)
  (hleft : ∀ i, q * c i = c i) (hright : ∀ i, c i * q = c i)
  (hanti : ∀ i j, c i * c j + c j * c i = 0)
  (hcar : ∀ i j, star (c i) * c j + c j * star (c i) = if i = j then q else 0)

include hanti in
lemma carFamily_square_zero (i : ℕ) : c i * c i = 0 := by
  have h : (2 : ℂ) • (c i * c i) = 0 := by rw [two_smul]; exact hanti i i
  exact (smul_eq_zero.mp h).resolve_left (by norm_num)

include hqstar hqq hleft hright hanti hcar in
lemma carFamily_parity_properties (i : ℕ) :
    star (carModeParity q (c i)) = carModeParity q (c i) ∧
      carModeParity q (c i) * carModeParity q (c i) = q ∧
      q * carModeParity q (c i) = carModeParity q (c i) ∧
      carModeParity q (c i) * q = carModeParity q (c i) ∧
      carModeParity q (c i) * c i = c i ∧ c i * carModeParity q (c i) = -(c i) := by
  apply carModeParity_properties q (c i) hqstar hqq (hleft i) (hright i)
    (carFamily_square_zero c hanti i)
  simpa only [ite_true] using hcar i i

include hleft hright hanti hcar in
lemma carFamily_parity_commute (i j : ℕ) (hij : i ≠ j) :
    Commute (carModeParity q (c i)) (c j) := by
  apply carModeParity_commute q (c i) (c j) (hleft j) (hright j) (hanti i j)
  simpa only [hij, ite_false] using hcar i j

include hqstar hqq hleft hright hanti hcar in
lemma carFamily_parities_commute (i j : ℕ) :
    Commute (carModeParity q (c i)) (carModeParity q (c j)) := by
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  have hc := carFamily_parity_commute q c hleft hright hanti hcar i j hij
  have hcs : Commute (carModeParity q (c i)) (star (c j)) := by
    simpa only [(carFamily_parity_properties q c hqstar hqq hleft hright hanti hcar i).1]
      using hc.star_star
  have hq : Commute (carModeParity q (c i)) q := by
    change carModeParity q (c i) * q = q * carModeParity q (c i)
    have hp := carFamily_parity_properties q c hqstar hqq hleft hright hanti hcar i
    rw [hp.2.2.1, hp.2.2.2.1]
  exact hq.sub_right ((hcs.mul_right hc).add_right (hcs.mul_right hc))

include hqstar hqq hleft hright hanti hcar in
lemma carParityPrefix_support (k : ℕ) :
    q * carParityPrefix q c k = carParityPrefix q c k ∧
      carParityPrefix q c k * q = carParityPrefix q c k := by
  induction k with
  | zero => exact ⟨hqq, hqq⟩
  | succ k ih =>
    have hp := carFamily_parity_properties q c hqstar hqq hleft hright hanti hcar k
    constructor
    · change q * (_ * _) = _
      rw [← mul_assoc, ih.1]
      rfl
    · change (_ * _) * q = _
      rw [mul_assoc, hp.2.2.2.1]
      rfl

include hqstar hqq hleft hright hanti hcar in
lemma carParityPrefix_commute_parity (k j : ℕ) :
    Commute (carParityPrefix q c k) (carModeParity q (c j)) := by
  induction k with
  | zero =>
    change q * carModeParity q (c j) = carModeParity q (c j) * q
    have hp := carFamily_parity_properties q c hqstar hqq hleft hright hanti hcar j
    rw [hp.2.2.1, hp.2.2.2.1]
  | succ k ih =>
    exact ih.mul_left (carFamily_parities_commute q c hqstar hqq hleft hright hanti hcar k j)

include hqstar hqq hleft hright hanti hcar in
lemma carParityPrefix_properties (k : ℕ) :
    star (carParityPrefix q c k) = carParityPrefix q c k ∧
      carParityPrefix q c k * carParityPrefix q c k = q := by
  induction k with
  | zero => exact ⟨hqstar, hqq⟩
  | succ k ih =>
    have hp := carFamily_parity_properties q c hqstar hqq hleft hright hanti hcar k
    have hc := carParityPrefix_commute_parity q c hqstar hqq hleft hright hanti hcar k k
    constructor
    · change star (_ * _) = _
      rw [star_mul, ih.1, hp.1, ← hc.eq]
      rfl
    · change (carParityPrefix q c k * carModeParity q (c k)) *
        (carParityPrefix q c k * carModeParity q (c k)) = q
      calc
        _ = carParityPrefix q c k *
            (carModeParity q (c k) * carParityPrefix q c k) * carModeParity q (c k) := by
          noncomm_ring
        _ = (carParityPrefix q c k * carParityPrefix q c k) *
            (carModeParity q (c k) * carModeParity q (c k)) := by rw [← hc.eq]; noncomm_ring
        _ = q := by rw [ih.2, hp.2.1, hqq]

include hqstar hqq hleft hright hanti hcar in
lemma carParityPrefix_commute (k l : ℕ) :
    Commute (carParityPrefix q c k) (carParityPrefix q c l) := by
  induction l with
  | zero =>
    change carParityPrefix q c k * q = q * carParityPrefix q c k
    have hs := carParityPrefix_support q c hqstar hqq hleft hright hanti hcar k
    rw [hs.1, hs.2]
  | succ l ih =>
    exact ih.mul_right (carParityPrefix_commute_parity q c hqstar hqq hleft hright hanti hcar k l)

include hleft hright hanti hcar in
lemma carParityPrefix_commute_mode (k j : ℕ) (hkj : k ≤ j) :
    Commute (carParityPrefix q c k) (c j) := by
  induction k with
  | zero => change q * c j = c j * q; rw [hleft j, hright j]
  | succ k ih =>
    exact (ih (by omega)).mul_left
      (carFamily_parity_commute q c hleft hright hanti hcar k j (by omega))

include hqstar hqq hleft hright hanti hcar in
lemma carParityPrefix_anticommute_mode (k j : ℕ) (hjk : j < k) :
    carParityPrefix q c k * c j + c j * carParityPrefix q c k = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hp := carFamily_parity_properties q c hqstar hqq hleft hright hanti hcar k
    by_cases hj : j = k
    · subst j
      have hc := carParityPrefix_commute_mode q c hleft hright hanti hcar k k le_rfl
      change (carParityPrefix q c k * carModeParity q (c k)) * c k +
        c k * (carParityPrefix q c k * carModeParity q (c k)) = 0
      calc
        _ = carParityPrefix q c k * (carModeParity q (c k) * c k) +
            (c k * carParityPrefix q c k) * carModeParity q (c k) := by noncomm_ring
        _ = carParityPrefix q c k * (carModeParity q (c k) * c k +
            c k * carModeParity q (c k)) := by rw [← hc.eq]; noncomm_ring
        _ = 0 := by rw [hp.2.2.2.2.1, hp.2.2.2.2.2, add_neg_cancel, mul_zero]
    · have hprev := ih (by omega)
      have hc := carFamily_parity_commute q c hleft hright hanti hcar k j (Ne.symm hj)
      change (carParityPrefix q c k * carModeParity q (c k)) * c j +
        c j * (carParityPrefix q c k * carModeParity q (c k)) = 0
      calc
        _ = (carParityPrefix q c k * c j + c j * carParityPrefix q c k) *
            carModeParity q (c k) := by rw [mul_assoc, hc.eq]; noncomm_ring
        _ = 0 := by rw [hprev, zero_mul]

include hqstar hqq hleft hright hanti hcar in
lemma carJordanWigner_support (k : ℕ) :
    q * carJordanWigner q c k = carJordanWigner q c k ∧
      carJordanWigner q c k * q = carJordanWigner q c k := by
  have hp := carParityPrefix_support q c hqstar hqq hleft hright hanti hcar k
  constructor
  · simp only [carJordanWigner, ← mul_assoc, hp.1]
  · simp only [carJordanWigner, mul_assoc, hright]

include hqstar hqq hleft hright hanti hcar in
lemma carJordanWigner_square_zero (k : ℕ) :
    carJordanWigner q c k * carJordanWigner q c k = 0 := by
  have hp := (carParityPrefix_properties q c hqstar hqq hleft hright hanti hcar k).2
  have hc := carParityPrefix_commute_mode q c hleft hright hanti hcar k k le_rfl
  unfold carJordanWigner
  calc
    _ = carParityPrefix q c k * (c k * carParityPrefix q c k) * c k := by noncomm_ring
    _ = (carParityPrefix q c k * carParityPrefix q c k) * (c k * c k) := by
      rw [← hc.eq]; noncomm_ring
    _ = 0 := by rw [hp, carFamily_square_zero c hanti, mul_zero]

include hqstar hqq hleft hright hanti hcar in
lemma carJordanWigner_gram (k : ℕ) :
    star (carJordanWigner q c k) * carJordanWigner q c k +
      carJordanWigner q c k * star (carJordanWigner q c k) = q := by
  have hp := carParityPrefix_properties q c hqstar hqq hleft hright hanti hcar k
  have hc := carParityPrefix_commute_mode q c hleft hright hanti hcar k k le_rfl
  have hcs : Commute (carParityPrefix q c k) (star (c k)) := by
    simpa only [hp.1] using hc.star_star
  have hfirst : star (carJordanWigner q c k) * carJordanWigner q c k = star (c k) * c k := by
    unfold carJordanWigner
    rw [star_mul, hp.1]
    calc
      _ = star (c k) * (carParityPrefix q c k * carParityPrefix q c k) * c k := by noncomm_ring
      _ = _ := by rw [hp.2, mul_assoc, hleft]
  have hsecond : carJordanWigner q c k * star (carJordanWigner q c k) = c k * star (c k) := by
    unfold carJordanWigner
    rw [star_mul, hp.1]
    calc
      _ = c k * (carParityPrefix q c k * star (c k)) * carParityPrefix q c k := by
        rw [hc.eq]; noncomm_ring
      _ = (c k * star (c k)) * (carParityPrefix q c k * carParityPrefix q c k) := by
        rw [hcs.eq]; noncomm_ring
      _ = _ := by
        rw [hp.2, mul_assoc]
        have hrightStar : star (c k) * q = star (c k) := by
          simpa only [star_mul, hqstar] using congrArg star (hleft k)
        rw [hrightStar]
  rw [hfirst, hsecond]
  simpa only [ite_true] using hcar k k

private lemma signedPrefix_commute (p p' a b : E)
    (hpp : Commute p p') (hpb : Commute p b)
    (hpa : p' * a + a * p' = 0) (hab : a * b + b * a = 0) :
    Commute (p * a) (p' * b) := by
  have hap : a * p' = -(p' * a) := eq_neg_of_add_eq_zero_right hpa
  have hab' : a * b = -(b * a) := eq_neg_of_add_eq_zero_left hab
  change (p * a) * (p' * b) = (p' * b) * (p * a)
  calc
    _ = p * (a * p') * b := by noncomm_ring
    _ = -((p * p') * (a * b)) := by rw [hap]; noncomm_ring
    _ = (p * p') * (b * a) := by rw [hab', mul_neg, neg_neg]
    _ = p' * (p * b) * a := by rw [hpp.eq]; noncomm_ring
    _ = (p' * b) * (p * a) := by rw [hpb.eq]; noncomm_ring

include hqstar hqq hleft hright hanti hcar in
lemma carJordanWigner_commute_of_lt (i j : ℕ) (hij : i < j) :
    Commute (carJordanWigner q c i) (carJordanWigner q c j) :=
  signedPrefix_commute _ _ _ _
    (carParityPrefix_commute q c hqstar hqq hleft hright hanti hcar i j)
    (carParityPrefix_commute_mode q c hleft hright hanti hcar i j hij.le)
    (carParityPrefix_anticommute_mode q c hqstar hqq hleft hright hanti hcar j i hij)
    (hanti i j)

include hqstar hqq hleft hright hanti hcar in
lemma carJordanWigner_commute (i j : ℕ) :
    Commute (carJordanWigner q c i) (carJordanWigner q c j) := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact carJordanWigner_commute_of_lt q c hqstar hqq hleft hright hanti hcar i j hij
  · subst j; exact Commute.refl _
  · exact (carJordanWigner_commute_of_lt q c hqstar hqq hleft hright hanti hcar j i hij).symm

include hqstar hqq hleft hright hanti hcar in
lemma carJordanWigner_star (i : ℕ) :
    star (carJordanWigner q c i) = carParityPrefix q c i * star (c i) := by
  have hp := (carParityPrefix_properties q c hqstar hqq hleft hright hanti hcar i).1
  have hc := carParityPrefix_commute_mode q c hleft hright hanti hcar i i le_rfl
  have hcs : Commute (carParityPrefix q c i) (star (c i)) := by
    simpa only [hp] using hc.star_star
  rw [carJordanWigner, star_mul, hp, hcs.eq]

include hqstar hqq hleft hright hanti hcar in
lemma carJordanWigner_star_commute_of_lt (i j : ℕ) (hij : i < j) :
    Commute (star (carJordanWigner q c i)) (carJordanWigner q c j) := by
  rw [carJordanWigner_star q c hqstar hqq hleft hright hanti hcar i]
  have hpa := congrArg star
    (carParityPrefix_anticommute_mode q c hqstar hqq hleft hright hanti hcar j i hij)
  simp only [star_add, star_mul, star_zero,
    (carParityPrefix_properties q c hqstar hqq hleft hright hanti hcar j).1] at hpa
  rw [add_comm] at hpa
  apply signedPrefix_commute _ _ _ _
    (carParityPrefix_commute q c hqstar hqq hleft hright hanti hcar i j)
    (carParityPrefix_commute_mode q c hleft hright hanti hcar i j hij.le) hpa
  simpa only [Nat.ne_of_lt hij, ite_false] using hcar i j

include hqstar hqq hleft hright hanti hcar in
lemma carJordanWigner_star_commute (i j : ℕ) (hij : i ≠ j) :
    Commute (star (carJordanWigner q c i)) (carJordanWigner q c j) := by
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact carJordanWigner_star_commute_of_lt q c hqstar hqq hleft hright hanti hcar i j hij
  · have h := (carJordanWigner_star_commute_of_lt q c hqstar hqq hleft hright hanti hcar j i hij).star_star.symm
    simpa only [star_star] using h

end Family

/-- The concrete disjoint-block family underlying the commuting coordinates. -/
def evenBlockFamily {n : ℕ} (r : Fin 2 × Fin n → E) (L : ℕ) (ζ : ℕ → ℂ) (i : ℕ) : E :=
  evenEigenMode r ((i + 1) * L) 0 L (ζ i)

lemma evenBlockFamily_CAR {n : ℕ} (q : E) (r : Fin 2 × Fin n → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
    (hsum : (∑ i, r i * star (r i)) = q)
    (L : ℕ) (hL : 0 < L) (ζ : ℕ → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1) :
    (∀ i, q * evenBlockFamily r L ζ i = evenBlockFamily r L ζ i) ∧
    (∀ i, evenBlockFamily r L ζ i * q = evenBlockFamily r L ζ i) ∧
    (∀ i j, evenBlockFamily r L ζ i * evenBlockFamily r L ζ j +
      evenBlockFamily r L ζ j * evenBlockFamily r L ζ i = 0) ∧
    (∀ i j, star (evenBlockFamily r L ζ i) * evenBlockFamily r L ζ j +
      evenBlockFamily r L ζ j * star (evenBlockFamily r L ζ i) = if i = j then q else 0) := by
  have hbase (i : ℕ) : 0 + L ≤ (i + 1) * L ∨ (i + 1) * L + L ≤ 0 := by
    left
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact (evenEigenMode_support q r hqstar hqq hrow hsum 0 _ L _).1
  · intro i
    exact (evenEigenMode_support q r hqstar hqq hrow hsum 0 _ L _).2
  · intro i j
    exact evenEigenMode_anticommute q r hqstar hqq hrow hsum 0 _ _ L hL
      (hbase i) (hbase j) _ _
  · intro i j
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      exact evenEigenMode_gram q r hqstar hqq hrow hsum 0 _ L hL (hbase i) _ (hζ i)
    · simp only [hij, ite_false]
      apply evenEigenMode_star_anticommute q r hqstar hqq hrow hsum 0 _ _ L hL
        (hbase i) (hbase j)
      rcases lt_or_gt_of_ne hij with hij | hij
      · left
        have : i + 2 ≤ j + 1 := by omega
        nlinarith
      · right
        have : j + 2 ≤ i + 1 := by omega
        nlinarith

end WeakPureInfiniteness

end

end OAI

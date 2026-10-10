import OAI.Analysis.OInfinity.ZeroCorner

namespace OAI

/-! # Finite Cuntz rows in the explicit complementary corner

Repeatedly splitting the first range of a relative Cuntz pair produces every
finite row size. All ranges still sum to the same projection `q`; the
complement `1 - q` is retained. The commutator estimate grows only linearly
with the number of splittings.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Right support follows from the relative isometry equation. -/
lemma relativeIsometry_mul_support (a q : E) (ha : star a * a = q)
    (hqstar : star q = q) (hqq : q * q = q) : a * q = a := by
  have hz : star (a * q - a) * (a * q - a) = 0 := by
    rw [star_sub, star_mul, hqstar]
    calc
      _ = q * (star a * a) * q - q * (star a * a) - (star a * a) * q + star a * a := by
        noncomm_ring
      _ = 0 := by simp only [ha, hqq]; abel
  exact sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)

lemma relativeCuntzPair_support (q a b : E) (hqstar : star q = q) (hqq : q * q = q)
    (ha : star a * a = q) (hb : star b * b = q) (hab : star a * b = 0)
    (hsum : a * star a + b * star b = q) :
    q * a = a ∧ a * q = a ∧ q * b = b ∧ b * q = b := by
  have haq := relativeIsometry_mul_support a q ha hqstar hqq
  have hbq := relativeIsometry_mul_support b q hb hqstar hqq
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  refine ⟨?_, haq, ?_, hbq⟩
  · rw [← hsum, add_mul, mul_assoc, ha, haq, mul_assoc, hba, mul_zero, add_zero]
  · rw [← hsum, add_mul, mul_assoc, hab, mul_zero, zero_add, mul_assoc, hb, hbq]

/-- At stage zero the row is the corner unit. Every successor replaces it
by `b` followed by the old row multiplied on the left by `a`. -/
def zeroCornerRow (q a b : E) : (n : ℕ) → Fin (n + 1) → E
  | 0, _ => q
  | n + 1, i => Fin.cases b (fun j => a * zeroCornerRow q a b n j) i

lemma zeroCornerRow_support (q a b : E) (hqq : q * q = q)
    (hqa : q * a = a) (hqb : q * b = b) (hbq : b * q = b) :
    ∀ n i, q * zeroCornerRow q a b n i = zeroCornerRow q a b n i ∧
      zeroCornerRow q a b n i * q = zeroCornerRow q a b n i := by
  intro n
  induction n with
  | zero => intro i; exact ⟨hqq, hqq⟩
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨hqb, hbq⟩
    · change q * (a * zeroCornerRow q a b n j) = a * zeroCornerRow q a b n j ∧
        (a * zeroCornerRow q a b n j) * q = a * zeroCornerRow q a b n j
      exact ⟨by rw [← mul_assoc, hqa], by rw [mul_assoc, (ih j).2]⟩

lemma zeroCornerRow_gram (q a b : E) (hqstar : star q = q) (hqq : q * q = q)
    (ha : star a * a = q) (hb : star b * b = q) (hab : star a * b = 0)
    (hqa : q * a = a) (hqb : q * b = b) (hbq : b * q = b) :
    ∀ n i j, star (zeroCornerRow q a b n i) * zeroCornerRow q a b n j =
      if i = j then q else 0 := by
  have hba : star b * a = 0 := by
    simpa only [star_mul, star_star, star_zero] using congrArg star hab
  intro n
  induction n with
  | zero =>
    intro i j
    have hij : i = j := by omega
    simp only [zeroCornerRow, hqstar, hqq, hij, ite_true]
  | succ n ih =>
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa only [zeroCornerRow, Fin.cases_zero, ite_true] using hb
      · simp only [zeroCornerRow, Fin.cases_zero, Fin.cases_succ, (Fin.succ_ne_zero j).symm,
          ite_false, ← mul_assoc, hba, zero_mul]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [zeroCornerRow, Fin.cases_zero, Fin.cases_succ, Fin.succ_ne_zero,
          ite_false, star_mul, mul_assoc, hab, mul_zero]
      · simp only [zeroCornerRow, Fin.cases_succ, star_mul, Fin.succ_inj]
        calc
          _ = star (zeroCornerRow q a b n i) * (star a * a) *
              zeroCornerRow q a b n j := by noncomm_ring
          _ = star (zeroCornerRow q a b n i) * (q * zeroCornerRow q a b n j) := by
            rw [ha, mul_assoc]
          _ = _ := by
            rw [(zeroCornerRow_support q a b hqq hqa hqb hbq n j).1, ih]

lemma zeroCornerRow_range_sum (q a b : E) (hqstar : star q = q) (hqq : q * q = q)
    (haq : a * q = a) (hsum : a * star a + b * star b = q) :
    ∀ n, ∑ i, zeroCornerRow q a b n i * star (zeroCornerRow q a b n i) = q := by
  intro n
  induction n with
  | zero =>
    change (∑ _i : Fin 1, q * star q) = q
    rw [Fin.sum_univ_one, hqstar, hqq]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [zeroCornerRow, Fin.cases_zero, Fin.cases_succ, star_mul]
    calc
      _ = b * star b + a * (∑ i, zeroCornerRow q a b n i *
          star (zeroCornerRow q a b n i)) * star a := by
        rw [Finset.mul_sum, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        noncomm_ring
      _ = q := by rw [ih, haq, add_comm, hsum]

lemma zeroCornerRow_norm_le (q a b : E) (hq : ‖q‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ∀ n i, ‖zeroCornerRow q a b n i‖ ≤ 1 := by
  intro n
  induction n with
  | zero => intro i; exact hq
  | succ n ih =>
    intro i
    refine Fin.cases hb (fun j => ?_) i
    exact (norm_mul_le _ _).trans (by
      simpa only [one_mul] using mul_le_mul ha (ih j)
        (norm_nonneg (zeroCornerRow q a b n j)) zero_le_one)

private lemma row_product_commutator_le (a b x : E)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖(a * b) * x - x * (a * b)‖ ≤ ‖a * x - x * a‖ + ‖b * x - x * b‖ := by
  have he : (a * b) * x - x * (a * b) =
      (a * x - x * a) * b + a * (b * x - x * b) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖(a * x - x * a) * b‖ + ‖a * (b * x - x * b)‖ := norm_add_le _ _
    _ ≤ ‖a * x - x * a‖ * ‖b‖ + ‖a‖ * ‖b * x - x * b‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ _ := add_le_add
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (norm_nonneg _))
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (norm_nonneg _))

/-- Each splitting costs at most one extra input commutator. -/
lemma zeroCornerRow_commutator_bound (q a b x : E) (δ γ : ℝ) (hδ : 0 ≤ δ) (hγ : 0 ≤ γ)
    (hq : ‖q‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hqc : ‖q * x - x * q‖ ≤ γ) (hac : ‖a * x - x * a‖ ≤ δ)
    (hbc : ‖b * x - x * b‖ ≤ δ) :
    ∀ n i, ‖zeroCornerRow q a b n i * x - x * zeroCornerRow q a b n i‖ ≤
      (n : ℝ) * δ + γ := by
  intro n
  induction n with
  | zero => intro i; simpa only [zeroCornerRow, Nat.cast_zero, zero_mul, zero_add] using hqc
  | succ n ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change ‖b * x - x * b‖ ≤ _
      have hn : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg n) hδ
      exact hbc.trans (by rw [Nat.cast_add, Nat.cast_one]; nlinarith)
    · change ‖(a * zeroCornerRow q a b n j) * x - x * (a * zeroCornerRow q a b n j)‖ ≤ _
      have hp := row_product_commutator_le a (zeroCornerRow q a b n j) x ha
        (zeroCornerRow_norm_le q a b hq ha hb n j)
      have hi := ih j
      rw [Nat.cast_add, Nat.cast_one]
      linarith

lemma zeroCornerRow_commutes (q a b x : E) (hq : Commute q x)
    (ha : Commute a x) (hb : Commute b x) :
    ∀ n i, Commute (zeroCornerRow q a b n i) x := by
  intro n
  induction n with
  | zero => intro i; exact hq
  | succ n ih =>
    intro i
    exact Fin.cases hb (fun j => ha.mul_left (ih j)) i


private lemma projection_norm_le_one (q : E) (hqstar : star q = q) (hqq : q * q = q) :
    ‖q‖ ≤ 1 := by
  have h : ‖star q * q‖ = ‖q‖ * ‖q‖ := CStarRing.norm_star_mul_self
  rw [hqstar, hqq] at h
  nlinarith [norm_nonneg q]

private lemma relativeIsometry_norm_le_one (a q : E) (ha : star a * a = q)
    (hq : ‖q‖ ≤ 1) : ‖a‖ ≤ 1 := by
  have h := congrArg norm ha
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg a]

private lemma row_star_commutator_norm (a x : E) :
    ‖star a * x - x * star a‖ = ‖a * star x - star x * a‖ := by
  rw [← norm_star (a * star x - star x * a)]
  simp only [star_sub, star_mul, star_star]
  exact norm_sub_rev _ _

private lemma pair_projection_commutator_le (q a b x : E) (δ : ℝ)
    (hsum : a * star a + b * star b = q) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hac : ‖a * x - x * a‖ ≤ δ) (hasc : ‖star a * x - x * star a‖ ≤ δ)
    (hbc : ‖b * x - x * b‖ ≤ δ) (hbsc : ‖star b * x - x * star b‖ ≤ δ) :
    ‖q * x - x * q‖ ≤ 4 * δ := by
  have he : q * x - x * q =
      ((a * star a) * x - x * (a * star a)) +
      ((b * star b) * x - x * (b * star b)) := by rw [← hsum]; noncomm_ring
  rw [he]
  have h₁ := row_product_commutator_le a (star a) x ha (by simpa only [norm_star] using ha)
  have h₂ := row_product_commutator_le b (star b) x hb (by simpa only [norm_star] using hb)
  exact (norm_add_le _ _).trans (by linarith)

/-- Every finite size occurs in a nonzero approximately central corner.
Choosing `m = 2*k+1` gives an even row of size `2*k+2`. -/
lemma exists_approximately_central_finite_corner_row [Nontrivial E]
    (s t : ℕ → E)
    (hs : ∀ i j, star (s i) * s j = if i = j then 1 else 0)
    (hc : ∀ i j, Commute (s i) (t j) ∧ Commute (s i) (star (t j)))
    (n m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (q : E) (v : Fin (m + 1) → E),
      q ≠ 0 ∧ star q = q ∧ q * q = q ∧
      (∀ i j, star (v i) * v j = if i = j then q else 0) ∧
      (∑ i, v i * star (v i)) = q ∧
      (∀ i, q * v i = v i ∧ v i * q = v i) ∧
      (∀ i k, k < n → ‖v i * s k - s k * v i‖ < δ ∧
        ‖v i * star (s k) - star (s k) * v i‖ < δ) ∧
      ∀ i k, Commute (v i) (t k) ∧ Commute (v i) (star (t k)) := by
  let η := δ / ((m : ℝ) + 5)
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨q, a, b, hqne, hqstar, hqq, haa, hbb, hab, hsum, hcomm, hother⟩ :=
    exists_approximately_central_zero_corner_pair s t hs hc n η hη
  obtain ⟨hqa, haq, hqb, hbq⟩ := relativeCuntzPair_support q a b hqstar hqq haa hbb hab hsum
  have hqn := projection_norm_le_one q hqstar hqq
  have han := relativeIsometry_norm_le_one a q haa hqn
  have hbn := relativeIsometry_norm_le_one b q hbb hqn
  refine ⟨q, zeroCornerRow q a b m, hqne, hqstar, hqq,
    zeroCornerRow_gram q a b hqstar hqq haa hbb hab hqa hqb hbq m,
    zeroCornerRow_range_sum q a b hqstar hqq haq hsum m,
    zeroCornerRow_support q a b hqq hqa hqb hbq m, ?_, ?_⟩
  · intro i k hk
    have h := hcomm k hk
    have hasc : ‖star a * s k - s k * star a‖ ≤ η := by
      rw [row_star_commutator_norm]
      exact h.2.2.1.le
    have hbsc : ‖star b * s k - s k * star b‖ ≤ η := by
      rw [row_star_commutator_norm]
      exact h.2.2.2.le
    have hascs : ‖star a * star (s k) - star (s k) * star a‖ ≤ η := by
      rw [row_star_commutator_norm, star_star]
      exact h.1.le
    have hbscs : ‖star b * star (s k) - star (s k) * star b‖ ≤ η := by
      rw [row_star_commutator_norm, star_star]
      exact h.2.1.le
    have hqc := pair_projection_commutator_le q a b (s k) η hsum han hbn
      h.1.le hasc h.2.1.le hbsc
    have hqcs := pair_projection_commutator_le q a b (star (s k)) η hsum han hbn
      h.2.2.1.le hascs h.2.2.2.le hbscs
    have h₁ := zeroCornerRow_commutator_bound q a b (s k) η (4 * η) hη.le
      (by positivity) hqn han hbn hqc h.1.le h.2.1.le m i
    have h₂ := zeroCornerRow_commutator_bound q a b (star (s k)) η (4 * η) hη.le
      (by positivity) hqn han hbn hqcs h.2.2.1.le h.2.2.2.le m i
    have hsmall : (m : ℝ) * η + 4 * η < δ := by
      have hmul : η * ((m : ℝ) + 5) = δ := by
        dsimp only [η]
        exact div_mul_cancel₀ δ (by positivity)
      nlinarith
    exact ⟨h₁.trans_lt hsmall, h₂.trans_lt hsmall⟩
  · intro i k
    have h := hother k
    have has : Commute (star a) (t k) := h.2.2.1.star_left
    have hbs : Commute (star b) (t k) := h.2.2.2.star_left
    have hqc : Commute q (t k) := by
      rw [← hsum]
      exact (h.1.mul_left has).add_left (h.2.1.mul_left hbs)
    have hqcs : Commute q (star (t k)) := by
      rw [← hsum]
      exact (h.2.2.1.mul_left h.1.star_star).add_left (h.2.2.2.mul_left h.2.1.star_star)
    exact ⟨zeroCornerRow_commutes q a b (t k) hqc h.1 h.2.1 m i,
      zeroCornerRow_commutes q a b (star (t k)) hqcs h.2.2.1 h.2.2.2 m i⟩

end WeakPureInfiniteness

end

end OAI

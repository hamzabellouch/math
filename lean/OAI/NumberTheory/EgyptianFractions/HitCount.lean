import Mathlib

namespace OAI
open scoped BigOperators

namespace Problem337.RandomProducts

variable {α : Type*} [DecidableEq α]

/-- All words of a fixed length over a finite alphabet. -/
def sampleWords (P : Finset α) (t : ℕ) : Finset (Fin t → α) :=
  Fintype.piFinset (fun _ => P)

/-- Words having at least `k` coordinates in the distinguished set. -/
def hitWords (P H : Finset α) (t k : ℕ) : Finset (Fin t → α) :=
  (sampleWords P t).filter (fun f => k ≤ (Finset.univ.filter (fun i => f i ∈ H)).card)

/-- Words required to hit the distinguished set at each specified coordinate. -/
def hitCylinder (P H : Finset α) {t : ℕ} (T : Finset (Fin t)) : Finset (Fin t → α) :=
  Fintype.piFinset (fun i => if i ∈ T then H else P)

omit [DecidableEq α] in
theorem card_hitCylinder (P H : Finset α) {t : ℕ} (T : Finset (Fin t)) :
    (hitCylinder P H T).card = H.card ^ T.card * P.card ^ (t - T.card) := by
  classical
  rw [hitCylinder, Fintype.card_piFinset]
  simp_rw [apply_ite Finset.card]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hc : (Finset.univ.filter (fun i : Fin t => i ∉ T)).card = t - T.card := by
    simpa only [Finset.card_compl, Fintype.card_fin] using congrArg Finset.card
      (show (Finset.univ.filter (fun i : Fin t => i ∉ T)) = Tᶜ by ext; simp)
  rw [hc]

/-- Elementary union bound over sets of `k` hit positions. -/
theorem card_hitWords_le (P H : Finset α) (t k : ℕ) :
    (hitWords P H t k).card ≤ t.choose k * H.card ^ k * P.card ^ (t - k) := by
  classical
  have hcover : hitWords P H t k ⊆
      (Finset.univ.powersetCard k).biUnion (hitCylinder P H) := by
    intro f hf
    obtain ⟨hfP, hfk⟩ := Finset.mem_filter.mp hf
    obtain ⟨T, hT, hTk⟩ := Finset.exists_subset_card_eq hfk
    apply Finset.mem_biUnion.mpr
    refine ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTk⟩, ?_⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    by_cases hi : i ∈ T
    · simp only [ite_eq_left hi]
      exact (Finset.mem_filter.mp (hT hi)).2
    · simp only [ite_eq_right hi]
      exact Fintype.mem_piFinset.mp hfP i
  calc
    (hitWords P H t k).card ≤
        ((Finset.univ.powersetCard k).biUnion (hitCylinder P H)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ T ∈ Finset.univ.powersetCard k, (hitCylinder P H T).card :=
      Finset.card_biUnion_le
    _ = ∑ _T ∈ Finset.univ.powersetCard k, H.card ^ k * P.card ^ (t - k) := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [card_hitCylinder, (Finset.mem_powersetCard.mp hT).2]
    _ = t.choose k * H.card ^ k * P.card ^ (t - k) := by
      simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      ring

/-- Normalized finite counting bound for independent uniform samples. -/
theorem hit_probability_le (P H : Finset α) (t k : ℕ) (hP : P.Nonempty) :
    ((hitWords P H t k).card : ℝ) / (P.card : ℝ) ^ t ≤
      ((t : ℝ) * (H.card : ℝ) / (P.card : ℝ)) ^ k := by
  have hPpos : 0 < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hP
  by_cases hk : k ≤ t
  · have hcard : (hitWords P H t k).card ≤ t ^ k * H.card ^ k * P.card ^ (t - k) :=
      (card_hitWords_le P H t k).trans
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.choose_le_pow t k)))
    have hcardR : ((hitWords P H t k).card : ℝ) ≤
        (t : ℝ) ^ k * (H.card : ℝ) ^ k * (P.card : ℝ) ^ (t - k) := by
      exact_mod_cast hcard
    calc
      ((hitWords P H t k).card : ℝ) / (P.card : ℝ) ^ t ≤
          ((t : ℝ) ^ k * (H.card : ℝ) ^ k * (P.card : ℝ) ^ (t - k)) /
            (P.card : ℝ) ^ t := div_le_div_of_nonneg_right hcardR (by positivity)
      _ = ((t : ℝ) * (H.card : ℝ) / (P.card : ℝ)) ^ k := by
        have hp : (P.card : ℝ) ^ t = (P.card : ℝ) ^ (t - k) * (P.card : ℝ) ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk]
        rw [hp, div_pow, mul_pow]
        field_simp
  · have hgt : t < k := Nat.lt_of_not_ge hk
    have hzero : (hitWords P H t k).card = 0 := by
      have h := card_hitWords_le P H t k
      simpa [Nat.choose_eq_zero_of_lt hgt] using h
    rw [hzero]
    simp only [Nat.cast_zero, zero_div]
    positivity

/-- Prime factors not dividing the modulus do not contribute to the common divisor.
The indexing retains multiplicities, as required for sampling with replacement. -/
theorem gcd_prod_dvd_hit_prod (s : Finset α) (p : α → ℕ) (u : ℕ)
    (hprime : ∀ i ∈ s, Nat.Prime (p i)) :
    Nat.gcd u (∏ i ∈ s, p i) ∣ ∏ i ∈ s, if p i ∣ u then p i else 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hpa := hprime a (Finset.mem_insert_self a s)
    have hps : ∀ i ∈ s, Nat.Prime (p i) := fun i hi => hprime i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine (Nat.gcd_mul_right_dvd_mul_gcd u (p a) (∏ i ∈ s, p i)).trans ?_
    apply Nat.mul_dvd_mul _ (ih hps)
    by_cases h : p a ∣ u
    · simp only [ite_eq_left h]
      exact Nat.gcd_dvd_right u (p a)
    · simp only [ite_eq_right h]
      have hpco : (p a).Coprime u := hpa.coprime_iff_not_dvd.mpr h
      rw [Nat.gcd_comm, hpco.gcd_eq_one]

/-- A common-divisor bound in terms of the number of hit samples. -/
theorem gcd_prod_le_pow_hit_count (s : Finset α) (p : α → ℕ) (u B : ℕ)
    (hprime : ∀ i ∈ s, Nat.Prime (p i)) (hB : ∀ i ∈ s, p i ≤ B) :
    Nat.gcd u (∏ i ∈ s, p i) ≤ B ^ (s.filter (fun i => p i ∣ u)).card := by
  classical
  have hpos : 0 < ∏ i ∈ s, if p i ∣ u then p i else 1 := by
    apply Finset.prod_pos
    intro i hi
    split_ifs
    · exact (hprime i hi).pos
    · exact Nat.zero_lt_one
  calc
    Nat.gcd u (∏ i ∈ s, p i) ≤ ∏ i ∈ s, if p i ∣ u then p i else 1 :=
      Nat.le_of_dvd hpos (gcd_prod_dvd_hit_prod s p u hprime)
    _ = ∏ i ∈ s with p i ∣ u, p i := (Finset.prod_filter _ _).symm
    _ ≤ ∏ _i ∈ s with p _i ∣ u, B := by
      apply Finset.prod_le_prod
      intro i hi
      exact hB i (Finset.mem_filter.mp hi).1
    _ = B ^ (s.filter (fun i => p i ∣ u)).card := Finset.prod_const _

/-- Uniform sampling estimate for a large gcd of a product of sampled primes.
This is the combinatorial part of the random-gcd exceptional-event bound. -/
theorem gcd_probability_le (P : Finset ℕ) (t k u B : ℕ)
    (hP : P.Nonempty) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hB : ∀ p ∈ P, p ≤ B) (hBone : 1 ≤ B) :
    (((sampleWords P t).filter (fun f =>
      B ^ (k - 1) < Nat.gcd u (∏ i, f i))).card : ℝ) / (P.card : ℝ) ^ t ≤
      ((t : ℝ) * ((P.filter (fun p => p ∣ u)).card : ℝ) / (P.card : ℝ)) ^ k := by
  classical
  have hsub : (sampleWords P t).filter (fun f =>
      B ^ (k - 1) < Nat.gcd u (∏ i, f i)) ⊆
      hitWords P (P.filter (fun p => p ∣ u)) t k := by
    intro f hf
    obtain ⟨hfP, hlarge⟩ := Finset.mem_filter.mp hf
    have hfp : ∀ i, f i ∈ P := Fintype.mem_piFinset.mp hfP
    apply Finset.mem_filter.mpr
    refine ⟨hfP, ?_⟩
    have heq : (Finset.univ.filter (fun i => f i ∈ P.filter (fun p => p ∣ u))) =
        (Finset.univ.filter (fun i => f i ∣ u)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfp i]
    rw [heq]
    by_contra hnot
    have hc : (Finset.univ.filter (fun i => f i ∣ u)).card ≤ k - 1 := by omega
    have hg := gcd_prod_le_pow_hit_count Finset.univ f u B
      (fun i _ => hprime (f i) (hfp i)) (fun i _ => hB (f i) (hfp i))
    exact hlarge.not_ge (hg.trans (pow_le_pow_right₀ hBone hc))
  calc
    _ ≤ ((hitWords P (P.filter (fun p => p ∣ u)) t k).card : ℝ) / (P.card : ℝ) ^ t := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := hit_probability_le P (P.filter (fun p => p ∣ u)) t k hP

/-- The numerical parameter choice for the exceptional gcd event in the random-products argument.
The threshold hypothesis is the denominator-cleared form of
`k ≥ 0.08 * V / (101 * log S)`. -/
theorem hit_probability_le_exp (P H : Finset α) (t k : ℕ) (S V : ℝ)
    (hP : P.Nonempty) (hS : 1 < S) (hV : 0 ≤ V)
    (ht : (t : ℝ) ≤ S) (hH : (H.card : ℝ) ≤ S)
    (hsize : S ^ 99 ≤ (P.card : ℝ))
    (hk : 8 * V ≤ 10100 * (k : ℝ) * Real.log S) :
    ((hitWords P H t k).card : ℝ) / (P.card : ℝ) ^ t ≤ Real.exp (-V / 20) := by
  have hSpos : 0 < S := by linarith
  have hprod : (t : ℝ) * (H.card : ℝ) ≤ S ^ 2 := by
    simpa only [pow_two] using mul_le_mul ht hH (Nat.cast_nonneg H.card) hSpos.le
  have hbase : (t : ℝ) * (H.card : ℝ) / (P.card : ℝ) ≤ 1 / S ^ 97 := by
    calc
      (t : ℝ) * (H.card : ℝ) / (P.card : ℝ) ≤ S ^ 2 / S ^ 99 :=
        div_le_div₀ (by positivity) hprod (by positivity) hsize
      _ = 1 / S ^ 97 := by
        rw [show (99 : ℕ) = 2 + 97 from rfl, pow_add]
        field_simp
  calc
    ((hitWords P H t k).card : ℝ) / (P.card : ℝ) ^ t ≤
        ((t : ℝ) * (H.card : ℝ) / (P.card : ℝ)) ^ k := hit_probability_le P H t k hP
    _ ≤ (1 / S ^ 97) ^ k := pow_le_pow_left₀ (by positivity) hbase k
    _ = Real.exp (-((97 * k : ℕ) : ℝ) * Real.log S) := by
      rw [one_div_pow, ← pow_mul, neg_mul, Real.exp_neg, Real.exp_nat_mul,
        Real.exp_log hSpos]
      simp only [one_div]
    _ ≤ Real.exp (-V / 20) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith

end Problem337.RandomProducts

end OAI

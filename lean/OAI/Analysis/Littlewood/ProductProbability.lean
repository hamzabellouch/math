import OAI.Analysis.Littlewood.Spreading

namespace OAI

universe uE uI

namespace AsymptoticallyMinimalLittlewood
namespace Nibble
open scoped BigOperators
open Finset

section ProductSpace
variable {E : Type uE} [Fintype E] [DecidableEq E]

def coinWeight (p : ℝ) (s : E → Bool) : ℝ :=
  ∏ e, if s e then p else 1 - p

def expectation (p : ℝ) (f : (E → Bool) → ℝ) : ℝ :=
  ∑ s, coinWeight p s * f s

def noHit (A : Finset E) (s : E → Bool) : ℝ :=
  ∏ e ∈ A, if s e then 0 else 1

lemma expectation_prod (p : ℝ) (g : E → Bool → ℝ) :
    expectation p (fun s ↦ ∏ e, g e (s e)) =
      ∏ e, (p * g e true + (1 - p) * g e false) := by
  dsimp [expectation, coinWeight]
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun e b ↦ (if b then p else 1 - p) * g e b)]
  simp

lemma coinWeight_sum (p : ℝ) : (∑ s : E → Bool, coinWeight p s) = 1 := by
  have h := expectation_prod (E := E) p (fun _ _ ↦ 1)
  simpa [expectation] using h

omit [DecidableEq E] in
lemma coinWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (s : E → Bool) :
    0 ≤ coinWeight p s := by
  apply Finset.prod_nonneg
  intro e he
  split_ifs <;> linarith

lemma expectation_const (p c : ℝ) : expectation (E := E) p (fun _ ↦ c) = c := by
  simp only [expectation, ← Finset.sum_mul, coinWeight_sum, one_mul]

lemma expectation_add (p : ℝ) (f g : (E → Bool) → ℝ) :
    expectation p (fun s ↦ f s + g s) = expectation p f + expectation p g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_sub (p : ℝ) (f g : (E → Bool) → ℝ) :
    expectation p (fun s ↦ f s - g s) = expectation p f - expectation p g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

lemma expectation_mul_const (p : ℝ) (f : (E → Bool) → ℝ) (c : ℝ) :
    expectation p (fun s ↦ f s * c) = expectation p f * c := by
  simp [expectation, ← mul_assoc, Finset.sum_mul]

lemma expectation_const_mul (p c : ℝ) (f : (E → Bool) → ℝ) :
    expectation p (fun s ↦ c * f s) = c * expectation p f := by
  simpa only [mul_comm c] using expectation_mul_const p f c

lemma expectation_sum {I : Type uI} (p : ℝ) (S : Finset I) (f : I → (E → Bool) → ℝ) :
    expectation p (fun s ↦ ∑ i ∈ S, f i s) = ∑ i ∈ S, expectation p (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

lemma expectation_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : (E → Bool) → ℝ} (h : ∀ s, f s ≤ g s) : expectation p f ≤ expectation p g := by
  exact Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (h s) (coinWeight_nonneg hp hp1 s)

lemma expectation_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f : (E → Bool) → ℝ} (hf : ∀ s, 0 ≤ f s) : 0 ≤ expectation p f := by
  simpa only [expectation_const] using expectation_mono hp hp1 hf

lemma exists_le_expectation {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (E → Bool) → ℝ) : ∃ s, f s ≤ expectation p f := by
  by_contra h
  push Not at h
  have hh : expectation (E := E) p (fun _ ↦ expectation p f) < expectation p f := by
    apply Finset.sum_lt_sum
    · intro s hs
      exact mul_le_mul_of_nonneg_left (h s).le (coinWeight_nonneg hp hp1 s)
    · have hex : ∃ s : E → Bool, 0 < coinWeight p s := by
        by_contra hn
        push Not at hn
        have hz : (∑ s : E → Bool, coinWeight p s) ≤ 0 := Finset.sum_nonpos fun s _ ↦ hn s
        rw [coinWeight_sum] at hz
        linarith
      obtain ⟨s, hs⟩ := hex
      exact ⟨s, Finset.mem_univ s, mul_lt_mul_of_pos_left (h s) hs⟩
  rw [expectation_const] at hh
  exact (lt_irrefl _ hh)

lemma noHit_eq (A : Finset E) (s : E → Bool) :
    noHit A s = if ∀ e ∈ A, s e = false then 1 else 0 := by
  dsimp [noHit]
  split_ifs with h
  · apply Finset.prod_eq_one
    intro e he
    simp [h e he]
  · push Not at h
    obtain ⟨e, he, hs⟩ := h
    apply Finset.prod_eq_zero he
    cases hh : s e <;> simp_all

lemma noHit_nonneg (A : Finset E) (s : E → Bool) : 0 ≤ noHit A s := by
  rw [noHit_eq]
  split_ifs <;> norm_num

lemma noHit_le_one (A : Finset E) (s : E → Bool) : noHit A s ≤ 1 := by
  rw [noHit_eq]
  split_ifs <;> norm_num

lemma noHit_union (A B : Finset E) (s : E → Bool) :
    noHit (A ∪ B) s = noHit A s * noHit B s := by
  simp only [noHit_eq, Finset.mem_union, or_imp, forall_and]
  split_ifs <;> simp_all

lemma expectation_noHit (p : ℝ) (A : Finset E) :
    expectation p (noHit A) = (1 - p) ^ A.card := by
  have heq (s : E → Bool) : noHit A s =
      ∏ e : E, if e ∈ A then (if s e then (0 : ℝ) else 1) else 1 := by
    rw [Finset.prod_ite_mem]
    simp [noHit]
  change expectation p (fun s ↦ noHit A s) = _
  simp_rw [heq]
  rw [expectation_prod p (fun e b ↦ if e ∈ A then (if b then (0 : ℝ) else 1) else 1)]
  calc
    _ = ∏ e : E, if e ∈ A then 1 - p else 1 := by
      apply Finset.prod_congr rfl
      intro e he
      by_cases h : e ∈ A <;> simp [h]
    _ = _ := by rw [Finset.prod_ite_mem]; simp

lemma one_sub_pow_le {p : ℝ} (_hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    1 - (1 - p) ^ n ≤ n * p := by
  have h := one_add_mul_le_pow (by linarith : -2 ≤ -p) n
  simp only [← sub_eq_add_neg] at h
  linarith

lemma noHit_covariance_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (A B : Finset E) :
    expectation p (fun s ↦ noHit A s * noHit B s) -
      expectation p (noHit A) * expectation p (noHit B) ≤ p * (A ∩ B).card := by
  simp_rw [← noHit_union, expectation_noHit]
  rw [← pow_add]
  have hc := Finset.card_union_add_card_inter A B
  rw [← hc, pow_add]
  have hq : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hpow : (1 - p) ^ (A ∪ B).card ≤ 1 := pow_le_one₀ hq hq1
  have hdec : 0 ≤ 1 - (1 - p) ^ (A ∩ B).card := by
    linarith [pow_le_one₀ hq hq1 (n := (A ∩ B).card)]
  have hmul := mul_le_mul_of_nonneg_right hpow hdec
  have hh := one_sub_pow_le hp hp1 (A ∩ B).card
  nlinarith

/-- The second-moment estimate used for every residual degree. Each test set
has size at most L and each independent edge-bit occurs in at most K tests. -/
lemma noHit_sum_variance {I : Type uI} [DecidableEq I] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset I) (A : I → Finset E)
    {K L : ℝ} (hK0 : 0 ≤ K) (hL : ∀ i ∈ S, ((A i).card : ℝ) ≤ L)
    (hK : ∀ e, ((S.filter fun i ↦ e ∈ A i).card : ℝ) ≤ K) :
    let Y : (E → Bool) → ℝ := fun s ↦ ∑ i ∈ S, noHit (A i) s
    expectation p (fun s ↦ (Y s - expectation p Y) ^ 2) ≤
      p * S.card * L * K := by
  classical
  dsimp only
  let Y : (E → Bool) → ℝ := fun s ↦ ∑ i ∈ S, noHit (A i) s
  change expectation p (fun s ↦ (Y s - expectation p Y) ^ 2) ≤ _
  have hid : expectation p (fun s ↦ (Y s - expectation p Y) ^ 2) =
      expectation p (fun s ↦ Y s ^ 2) - expectation p Y ^ 2 := by
    simp_rw [sub_sq]
    rw [expectation_add, expectation_sub, expectation_const,
      expectation_mul_const, expectation_const_mul]
    ring
  rw [hid]
  have hsq (s : E → Bool) : Y s ^ 2 = ∑ i ∈ S, ∑ j ∈ S, noHit (A i) s * noHit (A j) s := by
    dsimp [Y]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  simp_rw [hsq, expectation_sum]
  have hmean : expectation p Y ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, expectation p (noHit (A i)) * expectation p (noHit (A j)) := by
    dsimp [Y]
    rw [expectation_sum, pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hmean, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, p * ((A i ∩ A j).card : ℝ) :=
      Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦ noHit_covariance_le hp hp1 _ _
    _ ≤ ∑ i ∈ S, p * (L * K) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hp
      have hid' : (∑ j ∈ S, (A i ∩ A j).card) =
          ∑ e ∈ A i, (S.filter fun j ↦ e ∈ A j).card := by
        simp only [← Finset.filter_mem_eq_inter, Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
      have hb : (∑ j ∈ S, ((A i ∩ A j).card : ℝ)) ≤ L * K := by
        have hcast : (∑ j ∈ S, ((A i ∩ A j).card : ℝ)) =
            ∑ e ∈ A i, ((S.filter fun j ↦ e ∈ A j).card : ℝ) := by exact_mod_cast hid'
        rw [hcast]
        calc
          _ ≤ ∑ _e ∈ A i, K := Finset.sum_le_sum fun e _ ↦ hK e
          _ = (A i).card * K := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (hL i hi) hK0
      exact hb
    _ = _ := by simp; ring

lemma pow_bonferroni {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n - (1 - n * p) ≤ (n * p) ^ 2 / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hl := one_sub_pow_le hp hp1 n
    have hstep := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hp1)
    have he := mul_nonneg hp (sq_nonneg ((n : ℝ) * p))
    rw [pow_succ]
    push_cast
    nlinarith [sq_nonneg p]

lemma markov_indicator {p t : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (_ht : 0 ≤ t)
    (f : (E → Bool) → ℝ) (hf : ∀ s, 0 ≤ f s) :
    t * expectation p (fun s ↦ if t < f s then 1 else 0) ≤ expectation p f := by
  rw [← expectation_const_mul]
  apply expectation_mono hp hp1
  intro s
  split_ifs with h <;> simp_all
  exact h.le

lemma chebyshev_indicator {p t : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t)
    (f : (E → Bool) → ℝ) :
    t ^ 2 * expectation p (fun s ↦ if t < |f s - expectation p f| then 1 else 0) ≤
      expectation p (fun s ↦ (f s - expectation p f) ^ 2) := by
  rw [← expectation_const_mul]
  apply expectation_mono hp hp1
  intro s
  split_ifs with h
  · simp only [mul_one]
    nlinarith [sq_abs (f s - expectation p f)]
  · simp only [mul_zero]
    positivity

lemma exists_of_three_bad_bounds {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (P Q R : (E → Bool) → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (hP : expectation p (fun s ↦ if P s then 1 else 0) ≤ 1 / 4)
    (hQ : expectation p (fun s ↦ if Q s then 1 else 0) ≤ 1 / 4)
    (hR : expectation p (fun s ↦ if R s then 1 else 0) ≤ 1 / 4) :
    ∃ s, ¬ P s ∧ ¬ Q s ∧ ¬ R s := by
  obtain ⟨s, hs⟩ := exists_le_expectation hp hp1 (fun s ↦
    (if P s then (1 : ℝ) else 0) + (if Q s then 1 else 0) + (if R s then 1 else 0))
  rw [expectation_add, expectation_add] at hs
  refine ⟨s, ?_, ?_, ?_⟩ <;> intro h
  all_goals split_ifs at hs <;> linarith

lemma noHit_mean_error {I : Type uI} {p M B L : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hL : 0 ≤ L)
    (S : Finset I) (A : I → Finset E)
    (hcard : ∀ i ∈ S, |((A i).card : ℝ) - M| ≤ B)
    (hupper : ∀ i ∈ S, ((A i).card : ℝ) ≤ L) :
    |expectation p (fun s ↦ ∑ i ∈ S, noHit (A i) s) - S.card * (1 - p * M)| ≤
      S.card * (p * B + (p * L)^2 / 2) := by
  rw [expectation_sum]
  have hc : (S.card : ℝ) * (1 - p * M) = ∑ _i ∈ S, (1 - p * M) := by simp; ring
  rw [hc, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, |expectation p (noHit (A i)) - (1 - p * M)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, (p * B + (p * L)^2/2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [expectation_noHit]
      have hbon := pow_bonferroni hp hp1 (A i).card
      have hlo := one_sub_pow_le hp hp1 (A i).card
      have herr := hcard i hi
      have hbound := hupper i hi
      have hpv : 0 ≤ ((A i).card : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
      have hpl : ((A i).card : ℝ) * p ≤ L * p := mul_le_mul_of_nonneg_right hbound hp
      have hsq : (((A i).card : ℝ) * p)^2 ≤ (L*p)^2 := sq_le_sq₀ hpv (mul_nonneg hL hp) |>.mpr hpl
      have hm := mul_le_mul_of_nonneg_left (abs_le.mp herr).1 hp
      have hM := mul_le_mul_of_nonneg_left (abs_le.mp herr).2 hp
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg (p*L)]
    _ = _ := by simp; ring

/-- A Bernoulli indicator, for counting selected edges. -/
def selectedIndicator (e : E) (s : E → Bool) : ℝ := if s e then 1 else 0

omit [Fintype E] [DecidableEq E] in
lemma selectedIndicator_eq (e : E) (s : E → Bool) :
    selectedIndicator e s = 1 - noHit {e} s := by
  cases h : s e <;> simp [selectedIndicator, noHit, h]

omit [Fintype E] [DecidableEq E] in
lemma selectedIndicator_nonneg (e : E) (s : E → Bool) : 0 ≤ selectedIndicator e s := by
  dsimp [selectedIndicator]
  split_ifs <;> norm_num

lemma expectation_selected (p : ℝ) (e : E) : expectation p (selectedIndicator e) = p := by
  change expectation p (fun s ↦ selectedIndicator e s) = _
  simp_rw [selectedIndicator_eq]
  rw [expectation_sub, expectation_const, expectation_noHit]
  simp

lemma expectation_selected_mul (p : ℝ) (e f : E) (hef : e ≠ f) :
    expectation p (fun s ↦ selectedIndicator e s * selectedIndicator f s) = p^2 := by
  have heq (s : E → Bool) : selectedIndicator e s * selectedIndicator f s =
      1 - noHit {e} s - noHit {f} s + noHit ({e} ∪ {f}) s := by
    rw [noHit_union, selectedIndicator_eq, selectedIndicator_eq]
    ring
  simp_rw [heq]
  rw [expectation_add, expectation_sub, expectation_sub, expectation_const]
  simp only [expectation_noHit, Finset.card_singleton, pow_one]
  have hcard : ({e} ∪ {f} : Finset E).card = 2 := by simp [hef]
  rw [hcard]
  ring

/-- Simultaneous second-moment control of many local tests, one global test,
and a nonnegative collision count. No randomness remains in the conclusion. -/
lemma exists_controlled_outcome {I : Type uI} [DecidableEq I] {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (U : Finset I)
    (Y : I → (E → Bool) → ℝ) (Z W : (E → Bool) → ℝ)
    {V Vz M t b u c : ℝ} (ht : 0 < t) (hb : 0 < b) (hu : 0 < u) (hc : 0 < c)
    (hY : ∀ i ∈ U, expectation p (fun s ↦ (Y i s - expectation p (Y i))^2) ≤ V)
    (hZ : expectation p (fun s ↦ (Z s - expectation p Z)^2) ≤ Vz)
    (hW0 : ∀ s, 0 ≤ W s) (hW : expectation p W ≤ M)
    (hV : 4 * U.card * V ≤ t^2*b) (hVz : 4*Vz ≤ u^2) (hM : 4*M ≤ c) :
    ∃ s, (((U.filter fun i ↦ t < |Y i s - expectation p (Y i)|).card : ℝ) ≤ b) ∧
      |Z s - expectation p Z| ≤ u ∧ W s ≤ c := by
  classical
  let B : (E → Bool) → ℝ := fun s ↦
    ((U.filter fun i ↦ t < |Y i s - expectation p (Y i)|).card : ℝ)
  have hB0 (s : E → Bool) : 0 ≤ B s := Nat.cast_nonneg _
  have hB : t^2 * expectation p B ≤ U.card*V := by
    have heq : B = fun s ↦ ∑ i ∈ U, if t < |Y i s - expectation p (Y i)| then (1 : ℝ) else 0 := by
      funext s
      simp only [B, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [heq, expectation_sum, Finset.mul_sum]
    calc
      _ ≤ ∑ _i ∈ U, V := Finset.sum_le_sum fun i hi ↦
        (chebyshev_indicator hp hp1 ht.le (Y i)).trans (hY i hi)
      _ = _ := by simp
  have hP : expectation p (fun s ↦ if b < B s then 1 else 0) ≤ 1/4 := by
    have hm := markov_indicator hp hp1 hb.le B hB0
    have he := mul_le_mul_of_nonneg_left hm (sq_nonneg t)
    have hpos : 0 < t^2*b := mul_pos (sq_pos_of_pos ht) hb
    nlinarith
  have hQ : expectation p (fun s ↦ if u < |Z s - expectation p Z| then 1 else 0) ≤ 1/4 := by
    have hh := (chebyshev_indicator hp hp1 hu.le Z).trans hZ
    have hpos := sq_pos_of_pos hu
    nlinarith
  have hR : expectation p (fun s ↦ if c < W s then 1 else 0) ≤ 1/4 := by
    have hh := (markov_indicator hp hp1 hc.le W hW0).trans hW
    nlinarith
  obtain ⟨s, hsP, hsQ, hsR⟩ := exists_of_three_bad_bounds hp hp1
    (fun s ↦ b < B s) (fun s ↦ u < |Z s - expectation p Z|) (fun s ↦ c < W s)
    hP hQ hR
  exact ⟨s, le_of_not_gt hsP, le_of_not_gt hsQ, le_of_not_gt hsR⟩

end ProductSpace

end Nibble
end AsymptoticallyMinimalLittlewood

end OAI

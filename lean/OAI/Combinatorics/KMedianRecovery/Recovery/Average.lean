import Mathlib

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

noncomputable def average {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) : ℝ :=
  𝔼 ω, X ω

noncomputable def probability {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact average (fun ω => if P ω then 1 else 0)

noncomputable def sampleMean {Ω : Type*} (L : ℕ) (X : Ω → ℝ) (s : Fin L → Ω) : ℝ :=
  (∑ i, X (s i)) / L

section Average
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma average_congr {X Y : Ω → ℝ} (h : ∀ ω, X ω = Y ω) : average X = average Y :=
  Finset.expect_congr rfl (fun ω _ => h ω)

@[simp] lemma average_const [Nonempty Ω] (c : ℝ) : average (fun _ : Ω => c) = c :=
  Fintype.expect_const c

lemma average_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : average X ≤ average Y :=
  Finset.expect_le_expect (fun ω _ => h ω)

lemma average_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ average X :=
  Finset.expect_nonneg (fun ω _ => h ω)

lemma average_le [Nonempty Ω] {X : Ω → ℝ} {c : ℝ} (h : ∀ ω, X ω ≤ c) :
    average X ≤ c := Finset.expect_le Finset.univ_nonempty (fun ω _ => h ω)

lemma average_add (X Y : Ω → ℝ) :
    average (fun ω => X ω + Y ω) = average X + average Y :=
  Finset.expect_add_distrib _ _ _

lemma average_sub (X Y : Ω → ℝ) :
    average (fun ω => X ω - Y ω) = average X - average Y :=
  Finset.expect_sub_distrib _ _ _

lemma average_mul_const (X : Ω → ℝ) (c : ℝ) :
    average (fun ω => X ω * c) = average X * c :=
  (Finset.expect_mul _ _ _).symm

lemma average_const_mul (X : Ω → ℝ) (c : ℝ) :
    average (fun ω => c * X ω) = c * average X :=
  (Finset.mul_expect _ _ _).symm

lemma average_sum {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ) :
    average (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, average (X i) :=
  Finset.expect_sum_comm _ _ _

lemma average_prod (X : Ω × Ξ → ℝ) :
    average X = average (fun ω => average (fun ξ => X (ω,ξ))) := by
  simpa only [average, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ) X

lemma average_equiv (e : Ω ≃ Ξ) (X : Ω → ℝ) (Y : Ξ → ℝ)
    (h : ∀ ω, X ω = Y (e ω)) : average X = average Y :=
  Fintype.expect_equiv e X Y h

lemma average_pi_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (i : ι) (X : Ω → ℝ) : average (fun s : ι → Ω => X (s i)) = average X := by
  classical
  rw [average_equiv (Equiv.funSplitAt i Ω) (fun s : ι → Ω => X (s i)) (fun p => X p.1) (fun _ => rfl),
    average_prod]
  simp

lemma average_pi_mul {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (i j : ι) (hij : i ≠ j) (X Y : Ω → ℝ) :
    average (fun s : ι → Ω => X (s i) * Y (s j)) = average X * average Y := by
  classical
  have hji : j ≠ i := Ne.symm hij
  rw [average_equiv (Equiv.funSplitAt i Ω) (fun s : ι → Ω => X (s i) * Y (s j))
    (fun p => X p.1 * Y (p.2 ⟨j,hji⟩)) (fun _ => rfl), average_prod]
  simp_rw [average_const_mul, average_pi_apply]
  exact average_mul_const _ _

lemma variance_identity [Nonempty Ω] (X : Ω → ℝ) :
    average (fun ω => (X ω - average X)^2) = average (fun ω => (X ω)^2) - (average X)^2 := by
  rw [average_congr (Y := fun ω => X ω ^ 2 - 2 * average X * X ω + (average X)^2)
    (fun ω => by ring), average_add, average_sub, average_const_mul, average_const]
  ring

lemma bounded_variance [Nonempty Ω] (X : Ω → ℝ) {M : ℝ}
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ M) :
    average (fun ω => (X ω - average X)^2) ≤ M^2/4 := by
  have hs : average (fun ω => X ω ^ 2) ≤ M * average X := by
    rw [← average_const_mul]
    apply average_mono
    intro ω
    nlinarith [(hX ω).1, (hX ω).2]
  rw [variance_identity]
  nlinarith [sq_nonneg (average X - M/2)]

lemma sum_square {ι : Type*} [Fintype ι] (z : ι → ℝ) :
    (∑ i, z i)^2 = ∑ i, ∑ j, z i * z j := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma variance_sum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω] (X : Ω → ℝ) :
    average (fun s : ι → Ω => (∑ i, (X (s i) - average X))^2) =
      (Fintype.card ι : ℝ) * average (fun ω => (X ω - average X)^2) := by
  classical
  simp_rw [sum_square, average_sum]
  have hcenter : average (fun ω => X ω - average X) = 0 := by
    rw [average_sub, average_const, sub_self]
  have hm (i j : ι) :
      average (fun s : ι → Ω => (X (s i) - average X) * (X (s j) - average X)) =
        if i = j then average (fun ω => (X ω - average X)^2) else 0 := by
    split_ifs with hij
    · subst j
      simpa only [← pow_two] using average_pi_apply i (fun ω => (X ω - average X)^2)
    · rw [average_pi_mul i j hij (fun ω => X ω - average X) (fun ω => X ω - average X), hcenter, zero_mul]
  simp_rw [hm]
  simp

lemma sampleMean_variance [Nonempty Ω] (X : Ω → ℝ) (L : ℕ) (hL : 0 < L) :
    average (fun s : Fin L → Ω => (sampleMean L X s - average X)^2) =
      average (fun ω => (X ω - average X)^2) / L := by
  have hLR : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)
  have hm (s : Fin L → Ω) : sampleMean L X s - average X =
      (∑ i, (X (s i) - average X)) / L := by
    simp only [sampleMean, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp_rw [hm, div_pow, div_eq_mul_inv]
  rw [average_mul_const, variance_sum_pi, Fintype.card_fin]
  field_simp

end Average

section Probability
variable {Ω : Type*} [Fintype Ω]

lemma probability_nonneg (P : Ω → Prop) : 0 ≤ probability P := by
  classical
  apply average_nonneg
  intro ω
  split_ifs <;> norm_num

lemma probability_le_one [Nonempty Ω] (P : Ω → Prop) : probability P ≤ 1 := by
  classical
  apply average_le
  intro ω
  split_ifs <;> norm_num

lemma probability_mono {P Q : Ω → Prop} (h : ∀ ω, P ω → Q ω) :
    probability P ≤ probability Q := by
  classical
  apply average_mono
  intro ω
  split_ifs with hp hq hq <;> try norm_num
  exact absurd (h ω hp) hq

lemma probability_false : probability (fun _ : Ω => False) = 0 := by
  classical
  simp [probability, average]

lemma probability_compl [Nonempty Ω] (P : Ω → Prop) :
    probability (fun ω => ¬P ω) = 1 - probability P := by
  classical
  unfold probability
  rw [average_congr (Y := fun ω => 1 - if P ω then 1 else 0) (by
    intro ω
    by_cases hp : P ω <;> simp [hp]), average_sub, average_const]

lemma probability_union (P Q : Ω → Prop) :
    probability (fun ω => P ω ∨ Q ω) ≤ probability P + probability Q := by
  classical
  unfold probability
  rw [← average_add]
  apply average_mono
  intro ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq]

lemma probability_chebyshev (X : Ω → ℝ) (μ tol : ℝ) (htol : 0 < tol) :
    probability (fun ω => tol < |X ω - μ|) ≤
      average (fun ω => (X ω - μ)^2) / tol^2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos htol)).mpr
  rw [show probability (fun ω => tol < |X ω - μ|) * tol^2 =
    average (fun ω => (if tol < |X ω - μ| then (1:ℝ) else 0) * tol^2) from
    (average_mul_const _ _).symm]
  apply average_mono
  intro ω
  split_ifs with h
  · simp only [one_mul]
    have hs := mul_self_le_mul_self htol.le h.le
    simpa only [← pow_two, sq_abs] using hs
  · simpa only [zero_mul] using sq_nonneg (X ω - μ)

theorem sampleMean_error [Nonempty Ω]
    (X : Ω → ℝ) (L : ℕ) (hL : 0 < L) {M tol : ℝ}
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ M) (htol : 0 < tol) :
    probability (fun s : Fin L → Ω => tol < |sampleMean L X s - average X|)
      ≤ M^2 / (4 * L * tol^2) := by
  have hLR : (0:ℝ) < L := Nat.cast_pos.mpr hL
  have hc := probability_chebyshev (sampleMean L X) (average X) tol htol
  rw [sampleMean_variance X L hL] at hc
  have hv := div_le_div_of_nonneg_right (bounded_variance X hX) hLR.le
  have hv' := div_le_div_of_nonneg_right hv (sq_nonneg tol)
  refine hc.trans (hv'.trans_eq ?_)
  ring

lemma probability_congr {P Q : Ω → Prop} (h : ∀ ω, P ω ↔ Q ω) :
    probability P = probability Q := by
  classical
  apply average_congr
  intro ω
  simp only [h ω]

lemma probability_pi_apply {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (i : ι) (P : Ω → Prop) :
    probability (fun s : ι → Ω => P (s i)) = probability P := by
  classical
  exact average_pi_apply i (fun ω => if P ω then 1 else 0)

lemma probability_exists {ι : Type*} [Fintype ι] (P : ι → Ω → Prop) :
    probability (fun ω => ∃ i, P i ω) ≤ ∑ i, probability (P i) := by
  classical
  unfold probability
  rw [← average_sum]
  apply average_mono
  intro ω
  by_cases h : ∃ i, P i ω
  · obtain ⟨i,hi⟩ := h
    simp only [ite_eq_left (show ∃ index, P index ω from ⟨i,hi⟩)]
    calc
      (1:ℝ) = if P i ω then 1 else 0 := (ite_eq_left hi).symm
      _ ≤ ∑ j, if P j ω then 1 else 0 := by
        apply Finset.single_le_sum (f := fun j : ι => if P j ω then (1:ℝ) else 0)
        · intro j _
          split_ifs <;> norm_num
        · exact Finset.mem_univ i
  · simp only [ite_eq_right h]
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> norm_num

theorem simultaneous_sample_error {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (X : ι → Ω → ℝ) (L : ℕ) (hL : 0 < L) {M tol : ℝ}
    (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ M) (htol : 0 < tol) :
    probability (fun seed : ι → Fin L → Ω =>
      ∃ i, tol < |sampleMean L (X i) (seed i) - average (X i)|) ≤
      (Fintype.card ι : ℝ) * (M^2 / (4 * L * tol^2)) := by
  have hu := probability_exists (Ω := ι → Fin L → Ω)
    (fun i seed => tol < |sampleMean L (X i) (seed i) - average (X i)|)
  refine hu.trans ?_
  calc
    _ ≤ ∑ i : ι, M^2 / (4 * L * tol^2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [probability_pi_apply i (fun seed : Fin L → Ω =>
        tol < |sampleMean L (X i) seed - average (X i)|)]
      exact sampleMean_error (X i) L hL (hX i) htol
    _ = _ := by simp

theorem categorical_batch_error {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty Ω]
    (X : ι → Ω → ℝ) (L T a : ℕ) (hL : 0 < L) (hT : 0 < T) (ha : 0 < a)
    {M tau : ℝ} (hM : 0 < M) (htau : 0 < tau)
    (hX : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ M)
    (hcount : (T:ℝ) * Fintype.card ι * a^2 / (4 * tau^3) ≤ L) :
    probability (fun seed : ι → Fin L → Ω =>
      ∃ i, tau*M/a < |sampleMean L (X i) (seed i) - average (X i)|) ≤ tau/T := by
  have hLR : (0:ℝ) < L := Nat.cast_pos.mpr hL
  have hTR : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have haR : (0:ℝ) < a := Nat.cast_pos.mpr ha
  have htol : 0 < tau*M/a := by positivity
  refine (simultaneous_sample_error X L hL hX htol).trans ?_
  have hc := (div_le_iff₀ (show (0:ℝ) < 4*tau^3 by positivity)).mp hcount
  calc
    (Fintype.card ι : ℝ) * (M^2 / (4*L*(tau*M/a)^2)) =
        Fintype.card ι * (a:ℝ)^2 / (4*L*tau^2) := by
      field_simp
    _ ≤ tau/T := by
      apply (div_le_div_iff₀ (show (0:ℝ) < 4*L*tau^2 by positivity) hTR).mpr
      nlinarith

end Probability

lemma average_fin_succ {Ω : Type*} [Fintype Ω] (n : ℕ)
    (X : (Fin (n+1) → Ω) → ℝ) :
    average X = average (fun ω => average (fun s : Fin n → Ω => X (Fin.cons ω s))) := by
  calc
    average X = average (fun p : Ω × (Fin n → Ω) => X (Fin.cons p.1 p.2)) := by
      apply average_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Ω)).symm
      intro s
      exact congrArg X (Fin.cons_self_tail s).symm
    _ = _ := average_prod _

def adaptiveBad {S Ω : Type*} (f : S → Ω → S) (bad : S → Ω → Prop) :
    (n : ℕ) → S → (Fin n → Ω) → Prop
  | 0, _, _ => False
  | n+1, s, seed => bad s (seed 0) ∨ adaptiveBad f bad n (f s (seed 0)) (Fin.tail seed)

theorem adaptive_union_bound {S Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : S → Ω → S) (bad : S → Ω → Prop) (Inv : S → Prop) {p : ℝ}
    (hInv : ∀ s, Inv s → ∀ ω, Inv (f s ω))
    (hbad : ∀ s, Inv s → probability (bad s) ≤ p)
    (n : ℕ) (s : S) (hs : Inv s) :
    probability (adaptiveBad f bad n s) ≤ n * p := by
  classical
  induction n generalizing s with
  | zero => simp only [adaptiveBad, probability_false, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    unfold probability
    rw [average_fin_succ]
    have hrow (ω : Ω) :
        average (fun seed : Fin n → Ω =>
          if adaptiveBad f bad (n+1) s (Fin.cons ω seed) then (1:ℝ) else 0) ≤
          (if bad s ω then 1 else 0) + n*p := by
      change probability (fun seed : Fin n → Ω =>
        bad s ω ∨ adaptiveBad f bad n (f s ω) seed) ≤ _
      have hu := probability_union (fun _ : Fin n → Ω => bad s ω)
        (adaptiveBad f bad n (f s ω))
      have hp : probability (fun _ : Fin n → Ω => bad s ω) =
          (if bad s ω then (1:ℝ) else 0) := average_const _
      rw [hp] at hu
      exact hu.trans (add_le_add (le_refl _) (ih (f s ω) (hInv s hs ω)))
    have h := average_mono hrow
    rw [average_add, average_const] at h
    have hb := hbad s hs
    change average (fun ω => if bad s ω then (1:ℝ) else 0) ≤ p at hb
    simp only [Nat.cast_add, Nat.cast_one]
    linarith

theorem adaptive_categorical_error {S Ω ι : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]
    (X : S → ι → Ω → ℝ) (L T a : ℕ) (hL : 0 < L) (hT : 0 < T) (ha : 0 < a)
    {M tau : ℝ} (hM : 0 < M) (htau : 0 < tau)
    (f : S → (ι → Fin L → Ω) → S) (Inv : S → Prop)
    (hInv : ∀ s, Inv s → ∀ seed, Inv (f s seed))
    (hX : ∀ s, Inv s → ∀ i ω, 0 ≤ X s i ω ∧ X s i ω ≤ M)
    (hcount : (T:ℝ) * Fintype.card ι * a^2 / (4*tau^3) ≤ L)
    (s : S) (hs : Inv s) :
    probability (adaptiveBad f (fun u seed =>
      ∃ i, tau*M/a < |sampleMean L (X u i) (seed i) - average (X u i)|) T s) ≤ tau := by
  have h := adaptive_union_bound f
    (fun u seed => ∃ i, tau*M/a < |sampleMean L (X u i) (seed i) - average (X u i)|)
    Inv hInv (fun u hu => categorical_batch_error (X u) L T a hL hT ha hM htau (hX u hu) hcount)
    T s hs
  have hTR : (T:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hT)
  simpa only [mul_div_cancel₀ tau hTR] using h

lemma average_on_good {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (bad : Ω → Prop) {c : ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hgood : ∀ ω, ¬bad ω → c ≤ X ω) :
    (1 - probability bad) * c ≤ average X := by
  classical
  rw [← probability_compl bad]
  unfold probability
  rw [← average_mul_const]
  apply average_mono
  intro ω
  by_cases hb : bad ω
  · simpa [hb] using hX ω
  · simpa [hb] using hgood ω hb

end FiniteSampling
end MetricKMedianRecovery

end OAI

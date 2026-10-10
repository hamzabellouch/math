import OAI.Analysis.C0Absorption.Completion

namespace OAI

namespace C0Absorption

open scoped BigOperators NNReal ENNReal
noncomputable section
open Finset

section Signs

def realSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem realSign_true : realSign true = 1 := rfl
@[simp] theorem realSign_false : realSign false = -1 := rfl
@[simp] theorem abs_realSign (b : Bool) : |realSign b| = 1 := by cases b <;> norm_num

theorem sum_sign_sq (n : ℕ) (a : Fin n → ℝ) :
    ∑ ε : Fin n → Bool, (∑ i, realSign (ε i) * a i) ^ 2 =
      (2 : ℝ) ^ n * ∑ i, a i ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
      (fun p : Bool × (Fin n → Bool) =>
        (∑ i : Fin (n + 1), realSign ((Fin.consEquiv (fun _ => Bool)) p i) * a i) ^ 2)
      (fun ε : Fin (n + 1) → Bool => (∑ i, realSign (ε i) * a i) ^ 2)
      (fun _ => rfl)]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.consEquiv_apply,
      Fin.cons_zero, Fin.cons_succ, Fintype.sum_bool, realSign_true, realSign_false,
      one_mul, neg_one_mul]
    rw [← Finset.sum_add_distrib]
    have heq (x y : ℝ) : (x + y) ^ 2 + (-x + y) ^ 2 = 2 * x ^ 2 + 2 * y ^ 2 := by ring
    simp_rw [heq]
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, ih]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    ring

theorem finite_detector_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) (m : Fin n → X) (u : Fin n → X →ₗ[ℝ] ℝ)
    (α M δ : ℝ) (hα : 0 ≤ α) (_hM : 0 ≤ M)
    (hsum : ∀ ε : Fin n → Bool, ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (hdual : ∀ x, α * ∑ k, (u k x) ^ 2 ≤ ‖x‖ ^ 2)
    (hdetect : ∀ i, δ ^ 2 ≤ (u i (m i)) ^ 2) :
    α * (n : ℝ) * δ ^ 2 ≤ M ^ 2 := by
  classical
  have hdiag : (n : ℝ) * δ ^ 2 ≤ ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2 := by
    calc
      (n : ℝ) * δ ^ 2 = ∑ k : Fin n, δ ^ 2 := by simp
      _ ≤ ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hdetect k).trans (Finset.single_le_sum (fun i _ => sq_nonneg (u k (m i))) (mem_univ k))
  have havg : (2 : ℝ) ^ n * (α * ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) ≤
      (2 : ℝ) ^ n * M ^ 2 := by
    calc
      (2 : ℝ) ^ n * (α * ∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) =
          ∑ ε : Fin n → Bool, α * ∑ k : Fin n,
            (u k (∑ i : Fin n, realSign (ε i) • m i)) ^ 2 := by
        simp only [map_sum, map_smul, smul_eq_mul]
        conv_rhs => rw [← Finset.mul_sum, Finset.sum_comm]
        simp_rw [sum_sign_sq]
        rw [← Finset.mul_sum]
        ring
      _ ≤ ∑ ε : Fin n → Bool, M ^ 2 := by
        apply Finset.sum_le_sum
        intro ε hε
        exact (hdual _).trans (pow_le_pow_left₀ (norm_nonneg _) (hsum ε) 2)
      _ = (2 : ℝ) ^ n * M ^ 2 := by
        simp
  have ht : α * (∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) ≤ M ^ 2 :=
    le_of_mul_le_mul_left havg (by positivity)
  calc
    α * (n : ℝ) * δ ^ 2 = α * ((n : ℝ) * δ ^ 2) := by ring
    _ ≤ α * (∑ k : Fin n, ∑ i : Fin n, (u k (m i)) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiag hα
    _ ≤ M ^ 2 := ht

theorem no_infinite_detectors {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (u : ℕ → X →ₗ[ℝ] ℝ) (α M δ : ℝ)
    (hα : 0 < α) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (hdual : ∀ n x, α * ∑ k : Fin n, (u k x) ^ 2 ≤ ‖x‖ ^ 2)
    (hdetect : ∀ i, δ ≤ |u i (m i)|) : False := by
  have hbound (n : ℕ) : α * (n : ℝ) * δ ^ 2 ≤ M ^ 2 := by
    apply finite_detector_bound n (fun i => m i) (fun i => u i) α M δ hα.le hM
      (hsum n) (hdual n)
    intro i
    simpa only [sq_abs] using pow_le_pow_left₀ hδ.le (hdetect i) 2
  obtain ⟨n, hn⟩ := exists_nat_gt (M ^ 2 / (α * δ ^ 2))
  have hpos : 0 < α * δ ^ 2 := mul_pos hα (sq_pos_of_pos hδ)
  have hn' : M ^ 2 < (n : ℝ) * (α * δ ^ 2) := (div_lt_iff₀ hpos).mp hn
  nlinarith [hbound n]

def flipSign {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun ε j := if j = i then !(ε j) else ε j
  invFun ε j := if j = i then !(ε j) else ε j
  left_inv ε := by funext j; by_cases h : j = i <;> simp [h]
  right_inv ε := by funext j; by_cases h : j = i <;> simp [h]

@[simp] theorem realSign_not (b : Bool) : realSign (!b) = -realSign b := by
  cases b <;> norm_num

theorem signed_sum_sub_flip {X : Type*} [AddCommGroup X] [Module ℝ X]
    {n : ℕ} (m : Fin n → X) (ε : Fin n → Bool) (i : Fin n) :
    (∑ j, realSign (ε j) • m j) - (∑ j, realSign (flipSign i ε j) • m j) =
      (2 * realSign (ε i)) • m i := by
  classical
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp [flipSign, two_mul, add_smul]
  · intro j hj hji
    simp [flipSign, hji]
  · simp

theorem seminorm_sign_pair {X : Type*} [AddCommGroup X] [Module ℝ X]
    (q : Seminorm ℝ X) {n : ℕ} (m : Fin n → X) (ε : Fin n → Bool) (i : Fin n) :
    2 * (q (m i)) ^ 2 ≤
      (q (∑ j, realSign (ε j) • m j)) ^ 2 +
      (q (∑ j, realSign (flipSign i ε j) • m j)) ^ 2 := by
  have heq : q ((∑ j, realSign (ε j) • m j) -
      (∑ j, realSign (flipSign i ε j) • m j)) = 2 * q (m i) := by
    rw [signed_sum_sub_flip, map_smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_realSign]
    norm_num
  have ht := map_add_le_add q
    (∑ j, realSign (ε j) • m j) (-(∑ j, realSign (flipSign i ε j) • m j))
  rw [← sub_eq_add_neg, heq, map_neg_eq_map] at ht
  have hp := apply_nonneg q (m i)
  have ha := apply_nonneg q (∑ j, realSign (ε j) • m j)
  have hb := apply_nonneg q (∑ j, realSign (flipSign i ε j) • m j)
  nlinarith [sq_nonneg (q (∑ j, realSign (ε j) • m j) -
    q (∑ j, realSign (flipSign i ε j) • m j))]

theorem sum_sign_seminorm_sq_ge {X : Type*} [AddCommGroup X] [Module ℝ X]
    (q : Seminorm ℝ X) {n : ℕ} (m : Fin n → X) (i : Fin n) :
    (2 : ℝ) ^ n * (q (m i)) ^ 2 ≤
      ∑ ε : Fin n → Bool, (q (∑ j, realSign (ε j) • m j)) ^ 2 := by
  classical
  have h := Finset.sum_le_sum (s := Finset.univ) (fun ε _ => seminorm_sign_pair q m ε i)
  rw [Finset.sum_add_distrib] at h
  have heq : (∑ ε : Fin n → Bool, (q (∑ j, realSign (flipSign i ε j) • m j)) ^ 2) =
      ∑ ε : Fin n → Bool, (q (∑ j, realSign (ε j) • m j)) ^ 2 :=
    Fintype.sum_equiv (flipSign i) _ _ (fun _ => rfl)
  rw [heq] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  linarith

theorem sum_coordinate_choice_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hdom : ∀ (s : Finset ℕ) x, ∑ d ∈ s, (q d x) ^ 2 ≤ ‖x‖ ^ 2)
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (s : Finset ℕ) (index : ℕ → ℕ) :
    ∑ d ∈ s, (q d (m (index d))) ^ 2 ≤ M ^ 2 := by
  classical
  let n := s.sup index + 1
  have hlt (d : ℕ) (hd : d ∈ s) : index d < n :=
    Nat.lt_succ_of_le (Finset.le_sup hd)
  have hmain : (2 : ℝ) ^ n * (∑ d ∈ s, (q d (m (index d))) ^ 2) ≤
      (2 : ℝ) ^ n * M ^ 2 := by
    calc
      (2 : ℝ) ^ n * (∑ d ∈ s, (q d (m (index d))) ^ 2) =
          ∑ d ∈ s, (2 : ℝ) ^ n * (q d (m (index d))) ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ d ∈ s, ∑ ε : Fin n → Bool,
          (q d (∑ i : Fin n, realSign (ε i) • m i)) ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        exact sum_sign_seminorm_sq_ge (q d) (fun i : Fin n => m i) ⟨index d, hlt d hd⟩
      _ = ∑ ε : Fin n → Bool, ∑ d ∈ s,
          (q d (∑ i : Fin n, realSign (ε i) • m i)) ^ 2 := Finset.sum_comm
      _ ≤ ∑ ε : Fin n → Bool, M ^ 2 := by
        apply Finset.sum_le_sum
        intro ε hε
        exact (hdom s _).trans (pow_le_pow_left₀ (norm_nonneg _) (hsum n ε) 2)
      _ = (2 : ℝ) ^ n * M ^ 2 := by simp
  exact le_of_mul_le_mul_left hmain (by positivity)

theorem sum_ciSup_le_of_forall_choice {ι κ : Type*} [Nonempty κ]
    (a : ι → κ → ℝ) (s : Finset ι) (K : ℝ)
    (h : ∀ f : ι → κ, ∑ d ∈ s, a d (f d) ≤ K) :
    ∑ d ∈ s, ⨆ k, a d k ≤ K := by
  classical
  induction s using Finset.induction_on generalizing K with
  | empty => simpa using h (fun _ => Classical.choice (inferInstance : Nonempty κ))
  | @insert d s hd ih =>
    rw [Finset.sum_insert hd]
    rw [← le_sub_iff_add_le]
    apply ciSup_le
    intro k
    have ht : (∑ e ∈ s, ⨆ j, a e j) ≤ K - a d k := by
      apply ih
      intro f
      have hf := h (Function.update f d k)
      rw [Finset.sum_insert hd, Function.update_self] at hf
      have heq : (∑ e ∈ s, a e (Function.update f d k e)) = ∑ e ∈ s, a e (f e) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Function.update_of_ne (by intro heq; subst e; exact hd he)]
      rw [heq] at hf
      linarith
    linarith

theorem coordinate_envelope_summable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hdom : ∀ (s : Finset ℕ) x, ∑ d ∈ s, (q d x) ^ 2 ≤ ‖x‖ ^ 2)
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    Summable (fun d => ⨆ i : ℕ, (q d (m i)) ^ 2) ∧
      (∀ d i, (q d (m i)) ^ 2 ≤ ⨆ j : ℕ, (q d (m j)) ^ 2) := by
  have hb (d : ℕ) : BddAbove (Set.range (fun i : ℕ => (q d (m i)) ^ 2)) := by
    refine ⟨M ^ 2, ?_⟩
    rintro _ ⟨i, rfl⟩
    simpa using sum_coordinate_choice_le q hdom m M hsum {d} (fun _ => i)
  have hle (d i : ℕ) : (q d (m i)) ^ 2 ≤ ⨆ j : ℕ, (q d (m j)) ^ 2 :=
    le_ciSup (hb d) i
  constructor
  · apply summable_of_sum_le (c := M ^ 2)
    · intro d
      exact (sq_nonneg _).trans (hle d 0)
    · intro s
      apply sum_ciSup_le_of_forall_choice (fun d i => (q d (m i)) ^ 2)
      exact fun f => sum_coordinate_choice_le q hdom m M hsum s f
  · exact hle

theorem square_norm_tendsto_zero {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hq : ∀ x, Summable (fun d => (q d x) ^ 2))
    (hnorm : ∀ x, ‖x‖ ^ 2 = ∑' d, (q d x) ^ 2)
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (hzero : ∀ d, Filter.Tendsto (fun i => q d (m i)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun i => ‖m i‖ ^ 2) Filter.atTop (nhds 0) := by
  have hdom (s : Finset ℕ) (x : X) : ∑ d ∈ s, (q d x) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hnorm]
    exact Summable.sum_le_tsum s (fun _ _ => sq_nonneg _) (hq x)
  obtain ⟨hb, hle⟩ := coordinate_envelope_summable q hdom m M hsum
  have hp (d : ℕ) : Filter.Tendsto (fun i => (q d (m i)) ^ 2) Filter.atTop (nhds 0) := by
    simpa using (hzero d).pow 2
  have ht := tendsto_tsum_of_dominated_convergence hb hp
    (Filter.Eventually.of_forall fun i d => by
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hle d i)
  simpa only [← hnorm, tsum_zero] using ht

theorem exists_nonzero_coordinate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : ℕ → Seminorm ℝ X)
    (hq : ∀ x, Summable (fun d => (q d x) ^ 2))
    (hnorm : ∀ x, ‖x‖ ^ 2 = ∑' d, (q d x) ^ 2)
    (m : ℕ → X) (M r : ℝ) (hr : 0 < r)
    (hlower : ∀ i, r ≤ ‖m i‖)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M) :
    ∃ d, ¬ Filter.Tendsto (fun i => q d (m i)) Filter.atTop (nhds 0) := by
  by_contra! h
  have ht := square_norm_tendsto_zero q hq hnorm m M hsum h
  have hl : r ^ 2 ≤ (0 : ℝ) := ge_of_tendsto ht
    (Filter.Eventually.of_forall fun i => pow_le_pow_left₀ hr.le (hlower i) 2)
  nlinarith [sq_pos_of_pos hr]

end Signs

end
end C0Absorption

end OAI

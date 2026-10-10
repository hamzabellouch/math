import OAI.Probability.SATVariance.OmissionCompression

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma deletion_square_density {n r M : ℕ} (hr : 2 ≤ r) (hn : 2*(r+1) ≤ n)
    (i : Fin (M+1)) {B : ℝ} (hB : 0 ≤ B) (hM : (M : ℝ) ≤ B*n) :
    favg (fun cs : Fin (M+1) → Clause n (r+1) => (omittedTime i cs-finiteTime cs)^2) ≤
      deletionMomentC (r+1) (B*(r+1 : ℕ)^2) (2*B^2*(r+1 : ℕ)^4)*durationLog (r+1) M := by
  let := clause_nonempty n (r+1) (by omega)
  rw [favg_insertNth i]
  apply le_trans (favg_mono fun c : Clause n (r+1) => ?_) (le_of_eq (favg_const _))
  obtain ⟨e,a,hc⟩ := clause_root_presentation c
  have he := favg_equiv (Equiv.piCongrRight fun _ : Fin M => splitClauseEquiv e)
    (fun w : Fin M → Clause n (r+1) =>
      (omittedTime i (i.insertNth c w)-finiteTime (i.insertNth c w))^2)
  rw [← he]
  have hb := favg_mono (fun ps : Fin M → RootData (n-(r+1)) (r+1) =>
    pow_le_pow_left₀ (omittedTime_nonneg_diff i _) (deletion_difference_le_rewards e i c a hc ps) 2)
  exact hb.trans (rootRewards_square_density hr (by omega) e a hB hM)

lemma ell_eq_of_three {n : ℕ} (hn : 1 ≤ n) : ell 3 n = 1+Real.log n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp [ell, Real.log_mul (Real.exp_ne_zero _) hn0]

lemma ell_one_le (k n : ℕ) (hn : 1 ≤ n) : 1 ≤ ell k n := by
  by_cases hk : k = 3
  · subst k
    rw [ell_eq_of_three hn]
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    linarith
  · simp [ell, hk]

lemma durationLog_density {k n M : ℕ} (hn : 1 ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (hM : (M+1 : ℕ) ≤ B*(n : ℝ)) :
    durationLog k M ≤ (1+Real.log (B+1))*ell k n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hB0 : 0 < B+1 := by linarith
  have hlogB : 0 ≤ Real.log (B+1) := Real.log_nonneg (by linarith)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  by_cases hk : k = 3
  · subst k
    rw [durationLog, ite_eq_left rfl, ell_eq_of_three hn]
    have hm : (M : ℝ)+1 ≤ (B+1)*n := by push_cast at hM; nlinarith
    have hl := Real.log_le_log (by positivity : 0 < (M : ℝ)+1) hm
    rw [Real.log_mul (ne_of_gt hB0) (ne_of_gt hn0)] at hl
    nlinarith [mul_nonneg hlogB hlogn]
  · simp only [durationLog, ell, ite_eq_right hk, mul_one]
    linarith

lemma extend_upper_bound {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {k N : ℕ} (hk : 1 ≤ k)
    {C : ℝ} (hC : 0 ≤ C) (hlarge : ∀ n, N ≤ n → k ≤ n → f n ≤ C*n*ell k n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n, k ≤ n → f n ≤ D*n*ell k n := by
  let S := ∑ j ∈ Finset.range N, f j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => hf j)
  refine ⟨C+S,add_nonneg hC hS,fun n hkn => ?_⟩
  have hn : 1 ≤ n := hk.trans hkn
  have he := ell_one_le k n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hne : 1 ≤ (n : ℝ)*ell k n := by nlinarith
  by_cases hN : N ≤ n
  · have hh := hlarge n hN hkn
    nlinarith [mul_nonneg hS (show 0 ≤ (n : ℝ)*ell k n by positivity)]
  · have hs : f n ≤ S := Finset.single_le_sum (fun j _ => hf j) (Finset.mem_range.mpr (by omega))
    nlinarith [mul_nonneg hC (show 0 ≤ (n : ℝ)*ell k n by positivity),
      mul_le_mul_of_nonneg_left hne hS]

theorem capped_variance_upper (k : ℕ) (hk : 3 ≤ k) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, k ≤ n →
      variance (T B : Stream n k → ℝ) (streamLaw n k) ≤ C*n*ell k n := by
  cases k with
  | zero => omega
  | succ r =>
    have hr : 2 ≤ r := by omega
    let K := deletionMomentC (r+1) (B*(r+1 : ℕ)^2) (2*B^2*(r+1 : ℕ)^4)
    have hK : 0 ≤ K := deletionMomentC_nonneg hr _ _ (by positivity)
    let C := B*K*(1+Real.log (B+1))
    have hlogB : 0 ≤ Real.log (B+1) := Real.log_nonneg (by linarith)
    have hC : 0 ≤ C := by dsimp [C]; positivity
    apply extend_upper_bound (fun n => variance_nonneg _ _) (by omega : 1 ≤ r+1) hC
      (N := 2*(r+1))
    intro n hn _
    have hn1 : 1 ≤ n := by omega
    have hcap : (cap n B : ℝ) ≤ B*n := Nat.floor_le (by positivity)
    have hh := capped_coordinate_omission (by omega : r+1 ≤ n) B
    cases he : cap n B with
    | zero =>
      rw [he] at hh
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hh
      exact hh.trans (by have hh' := ell_one_le (r+1) n hn1; dsimp [C]; positivity)
    | succ M =>
      have hM : (M : ℝ) ≤ B*n := by rw [he] at hcap; push_cast at hcap; linarith
      have hb := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (M+1)))) =>
        deletion_square_density hr hn i hB.le hM)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
      rw [he] at hh hcap
      have htime := durationLog_density (k := r+1) hn1 hB.le hcap
      have ht := mul_le_mul_of_nonneg_left htime (mul_nonneg (Nat.cast_nonneg (M+1)) hK)
      have hf := mul_le_mul_of_nonneg_right hcap
        (show 0 ≤ K*((1+Real.log (B+1))*ell (r+1) n) by
          have he := ell_one_le (r+1) n hn1
          positivity)
      change _ ≤ C*n*ell (r+1) n
      change _ ≤ ((M+1 : ℕ) : ℝ)*(K*durationLog (r+1) M) at hb
      dsimp only [C]
      nlinarith [hh.trans hb]

end RandomKSAT

end

end OAI

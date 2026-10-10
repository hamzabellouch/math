import OAI.MeasureTheory.SelfSimilar.EntropyBudget

namespace OAI

universe uα uβ

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory

theorem grid_le_averaged_add_log_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    grid μ s u ≤ averaged μ s+Real.log 2 := by
  have hh := intervalIntegral.integral_mono zero_le_one
    (intervalIntegrable_const (c := grid μ s u))
    ((grid_intervalIntegrable μ hμ hs 0 1).add intervalIntegrable_const)
    (fun v => grid_le_grid_add_log_two μ hμ hs hs le_rfl u v)
  rw [intervalIntegral.integral_const,intervalIntegral.integral_add
    (grid_intervalIntegrable μ hμ hs 0 1) intervalIntegrable_const,
    intervalIntegral.integral_const,← averaged_eq_intervalIntegral] at hh
  simpa only [sub_zero,one_smul] using hh

end EntropyRateDimension.MeasureEntropy

namespace EntropyRateDimension.Typed
open FairPairs MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]

noncomputable def fineScale (A : ℝ) (n : ℕ) : ℝ := (2 : ℝ)^(-⌈A*n⌉)
noncomputable def bandStart (A : ℝ) (n : ℕ) : ℤ := ⌈A*n⌉-1

theorem fineScale_pos (A : ℝ) (n : ℕ) : 0 < fineScale A n := zpow_pos (by norm_num) _

theorem fineScale_lt_one {A : ℝ} (hA : 0 < A) {n : ℕ} (hn : 0 < n) : fineScale A n < 1 := by
  have ht : 0 < ⌈A*n⌉ := Int.ceil_pos.mpr (mul_pos hA (by exact_mod_cast hn))
  change (2 : ℝ)^(-⌈A*n⌉) < (2 : ℝ)^(0 : ℤ)
  exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mpr (by omega)

theorem fineScale_log (A : ℝ) (n : ℕ) :
    Real.log (1/fineScale A n)=(⌈A*n⌉ : ℝ)*Real.log 2 := by
  rw [one_div,Real.log_inv,fineScale,Real.log_zpow,Int.cast_neg,neg_mul,neg_neg]

theorem expected_loss_linear (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    {D C A : ℝ} (hD : 0 ≤ D) (hA : 0 < A)
    (hb : ∀ s, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C)
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ)*(S.entropyRate*Real.log 2-Real.log (Fintype.card β)-D*A*Real.log 2)-
        (D*Real.log 2+C+2*Real.log 2) ≤
      ∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w (fineScale A n) := by
  obtain ⟨B,hB,hc⟩ := S.selfSimilar_compact μ hμ
  have hc' : CompactlyCarried μ := ⟨B,hB.le,hc⟩
  have he := expected_entropyLoss_lower S tag hr μ hμ hc' n (fineScale_pos A n)
  have hg : grid μ (fineScale A n) 0 ≤ D*Real.log (1/fineScale A n)+C+Real.log 2 := by
    have h1 := grid_le_averaged_add_log_two μ hc' (fineScale_pos A n) 0
    have h2 := hb _ (fineScale_pos A n) (fineScale_lt_one hA hn)
    linarith
  rw [fineScale_log] at hg
  have hh := S.entropyRate_le (n-1)
  rw [Nat.sub_add_cancel hn] at hh
  have hh' := mul_le_mul_of_nonneg_right
    ((le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ)<n)).mp hh)
    (Real.log_pos (by norm_num : (1 : ℝ)<2)).le
  have hhceil := mul_le_mul_of_nonneg_right (Int.ceil_lt_add_one (A*n)).le
    (mul_nonneg hD (Real.log_pos (by norm_num : (1 : ℝ)<2)).le)
  nlinarith

omit [Fintype β] in
theorem discarded_loss_bound (S : System α) (tag : α → β)
    {A' : ℝ} (hA' : S.lyapunov < A') {n : ℕ} (hn : 0 < n) (ρ : ℝ) :
    (∑ w : Fin n → α, if A'*n < S.wordDepth w then
      S.wordWeight w*entropyLoss S tag w ρ else 0) ≤
        Real.log (Fintype.card α)*S.depthVariance/(A'-S.lyapunov)^2 := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hcard : (1 : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  have hl : 0 ≤ Real.log (Fintype.card α) := Real.log_nonneg hcard
  have hbound := S.depth_bad_mass_bound hA' hn
  calc
    _ ≤ (n : ℝ)*Real.log (Fintype.card α)*
        ∑ w : Fin n → α, if A'*n < S.wordDepth w then S.wordWeight w else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro w _
      split_ifs
      · simpa only [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left (entropyLoss_le S tag w ρ) (S.wordWeight_pos w).le
      · simp
    _ ≤ (n : ℝ)*Real.log (Fintype.card α)*
        (S.depthVariance/((n : ℝ)*(A'-S.lyapunov)^2)) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg hnR.le hl)
    _ = _ := by field_simp

noncomputable def retainedLoss (S : System α) (tag : α → β) (A A' : ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, if S.wordDepth w ≤ A'*n then
    S.wordWeight w*entropyLoss S tag w (fineScale A n) else 0

theorem retained_loss_linear (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    {D C A A' : ℝ} (hD : 0 ≤ D) (hA : 0 < A) (hA' : S.lyapunov < A')
    (hb : ∀ s, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C)
    (hgap : D*A*Real.log 2 < S.entropyRate*Real.log 2-Real.log (Fintype.card β)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      ε*n ≤ retainedLoss S tag A A' n := by
  classical
  let γ := S.entropyRate*Real.log 2-Real.log (Fintype.card β)-D*A*Real.log 2
  have hγ : 0 < γ := sub_pos.mpr hgap
  let K := D*Real.log 2+C+2*Real.log 2+
    Real.log (Fintype.card α)*S.depthVariance/(A'-S.lyapunov)^2
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (2*K/γ))
  have hNpos : 0 < N := by
    have := (le_max_left _ _).trans_lt hN
    exact_mod_cast (lt_trans zero_lt_one this)
  refine ⟨γ/2,by positivity,N,hNpos,fun n hn => ?_⟩
  have hn0 := hNpos.trans_le hn
  have he := expected_loss_linear S tag hr μ hμ hD hA hb hn0
  have hd := discarded_loss_bound S tag hA' hn0 (fineScale A n)
  have hid : retainedLoss S tag A A' n+
      (∑ w : Fin n → α, if A'*n < S.wordDepth w then
        S.wordWeight w*entropyLoss S tag w (fineScale A n) else 0)=
      ∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w (fineScale A n) := by
    rw [retainedLoss,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : S.wordDepth w ≤ A'*n <;> simp [h,not_lt_of_ge,lt_of_not_ge]
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hNK := (div_lt_iff₀ hγ).mp ((le_max_right _ _).trans_lt hN)
  change (n : ℝ)*γ-(D*Real.log 2+C+2*Real.log 2) ≤ _ at he
  dsimp only [K] at hNK
  nlinarith

end EntropyRateDimension.Typed

end OAI

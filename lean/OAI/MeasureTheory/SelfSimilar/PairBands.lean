import OAI.MeasureTheory.SelfSimilar.TypedSumset

namespace OAI

universe uα uβ

namespace EntropyRateDimension
open scoped BigOperators Topology
open Filter

theorem exists_nat_log_small {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ k : ℕ, 0 < k ∧ K*Real.log (k+1) < ε*k := by
  have ht : Tendsto (fun k : ℕ => K*(Real.log ((k : ℝ)+1)/(k : ℝ))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    simpa only [pow_one,one_mul,Function.comp_apply,add_neg_cancel_right,mul_zero] using h.const_mul K
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  let k := max N 1
  have hk : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  refine ⟨k,hk,?_⟩
  have hh := hN k (le_max_left _ _)
  have hp : (0 : ℝ)<k := by exact_mod_cast hk
  rw [← mul_div_assoc] at hh
  exact (div_lt_iff₀ hp).mp hh

namespace Typed
open FairPairs
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [DecidableEq β]

noncomputable def pairBudget (S : System α) (tag : α → β) (A' : ℝ)
    (a B : ℤ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → α, if S.wordDepth w ≤ A'*n then S.wordWeight w*
    ∑ ℓ ∈ Finset.Icc a B, capacity (law S tag w) ℓ else 0

omit [Nonempty α] in
theorem fineScale_band_condition (A : ℝ) (n : ℕ) (ℓ : ℤ) :
    (2 : ℝ)^(-ℓ) ≤ 2*fineScale A n ↔ bandStart A n ≤ ℓ := by
  have he : 2*fineScale A n=(2 : ℝ)^(1-⌈A*n⌉) := by
    rw [sub_eq_add_neg,zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one]
    rfl
  rw [he,zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)]
  dsimp only [bandStart]
  omega

omit [Nonempty α] in
theorem exists_band_pair_bound (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (A : ℝ) (n k : ℕ) (hk : 1 ≤ k) :
    ∃ B : ℤ, bandStart A n ≤ B ∧ ∀ w : Fin n → α,
      (k : ℝ)*entropyLoss S tag w (fineScale A n) ≤
        (n : ℝ)*Fintype.card α*Real.log (k+1)+60000*k^4*Real.log 2*
          ∑ ℓ ∈ Finset.Icc (bandStart A n) B, capacity (law S tag w) ℓ := by
  classical
  let J := insert (bandStart A n) (Finset.univ.biUnion (fun w : Fin n → α => (law S tag w).bandSupport))
  have hJ : J.Nonempty := Finset.insert_nonempty _ _
  let B := J.max' hJ
  have hab : bandStart A n ≤ B := Finset.le_max' J _ (Finset.mem_insert_self _ _)
  refine ⟨B,hab,fun w => ?_⟩
  have hh := pair_bound_natural (law S tag w) k hk (fineScale A n) (fineScale_pos A n)
  have hs : ∑ ℓ ∈ (law S tag w).bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*fineScale A n),
      capacity (law S tag w) ℓ ≤
      ∑ ℓ ∈ Finset.Icc (bandStart A n) B, capacity (law S tag w) ℓ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ℓ hℓ
      obtain ⟨hℓ,hrℓ⟩ := Finset.mem_filter.mp hℓ
      apply Finset.mem_Icc.mpr
      refine ⟨(fineScale_band_condition A n ℓ).mp hrℓ,?_⟩
      apply Finset.le_max' J ℓ
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨w,Finset.mem_univ _,hℓ⟩)
    · intro ℓ _ _
      exact capacity_nonneg _ _
  have hc : 0 ≤ 60000*(k : ℝ)^4*Real.log 2 := by positivity
  have hl := sumset_log_bound S tag hr w k
  have hid : entropyLoss S tag w (fineScale A n)=
      FiniteEntropy.entropy (law S tag w).support (law S tag w).prob-
        FiniteEntropy.observableEntropy (law S tag w).support (law S tag w).prob (fun x => ⌊x/fineScale A n⌋) := by
    dsimp only [entropyLoss,Law.shannonEntropy,Law.gridEntropy]
    field_simp
  rw [hid]
  exact hh.trans (add_le_add hl (mul_le_mul_of_nonneg_left hs hc))

omit [Nonempty α] in
theorem pair_bands_of_retained_loss (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (A A' : ℝ) {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (he : ∀ n, N ≤ n → ε*n ≤ retainedLoss S tag A A' n) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, N ≤ n → ∃ B : ℤ, bandStart A n ≤ B ∧
      c*n ≤ pairBudget S tag A' (bandStart A n) B n := by
  classical
  obtain ⟨k,hk,hl⟩ := exists_nat_log_small hε (Fintype.card α)
  let K : ℝ := Fintype.card α*Real.log (k+1)
  let C : ℝ := 60000*k^4*Real.log 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hgap : 0 < ε*k-K := sub_pos.mpr hl
  refine ⟨(ε*k-K)/C,div_pos hgap hC,fun n hn => ?_⟩
  obtain ⟨B,hB,hb⟩ := exists_band_pair_bound S tag hr A n k hk
  refine ⟨B,hB,?_⟩
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith))
  have hp : (k : ℝ)*retainedLoss S tag A A' n ≤ (n : ℝ)*K+C*pairBudget S tag A' (bandStart A n) B n := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun (w : Fin n → α) _ =>
      show (k : ℝ)*(if S.wordDepth w ≤ A'*n then S.wordWeight w*entropyLoss S tag w (fineScale A n) else 0) ≤
        S.wordWeight w*((n : ℝ)*K)+C*(if S.wordDepth w ≤ A'*n then S.wordWeight w*
          ∑ ℓ ∈ Finset.Icc (bandStart A n) B, capacity (law S tag w) ℓ else 0) from by
        split_ifs
        · have h := mul_le_mul_of_nonneg_left (hb w) (S.wordWeight_pos w).le
          dsimp only [K,C]
          nlinarith
        · simp only [mul_zero,add_zero]
          exact mul_nonneg (S.wordWeight_pos w).le (mul_nonneg (Nat.cast_nonneg _) hK))
    simpa only [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.sum_mul,
      S.wordWeight_sum,one_mul,retainedLoss,pairBudget] using hh
  have hh := mul_le_mul_of_nonneg_left (he n hn) (by positivity : (0 : ℝ)≤k)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hC).mpr
  nlinarith

end Typed
end EntropyRateDimension

end OAI

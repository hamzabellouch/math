import OAI.MeasureTheory.SelfSimilar.BlockWords

namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open FiniteEntropy FairPairs FiniteCondition MeasureEntropy MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] [DecidableEq β]

theorem expected_entropy_lower (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v) (n : ℕ) :
    S.walkEntropy n*Real.log 2-(n : ℝ)*Real.log (Fintype.card β) ≤
      (∑ w : Fin n → α, S.wordWeight w*(law S tag w).shannonEntropy)*Real.log 2 := by
  classical
  rw [show (∑ w : Fin n → α, S.wordWeight w*(law S tag w).shannonEntropy)*Real.log 2=
    conditionalEntropy Finset.univ S.wordWeight (fun w => (S.completeMap w).2) (tagWord tag) from
      law_entropy_mean S.wordWeight S.wordWeight_pos (tagWord tag) _]
  have he := observableEntropy_le_of_fibers Finset.univ (S.wordWeight (n := n))
    S.completeMap (fun w => ((S.completeMap w).2,tagWord tag w))
    (fun w _ => (S.wordWeight_pos w).le) (by
      intro w _ v _ h
      apply Prod.ext
      · rw [S.completeMap_slope,S.completeMap_slope]
        exact Finset.prod_congr rfl (fun j _ => hr _ _ (congrFun (Prod.mk.inj h).2 j))
      · exact (Prod.mk.inj h).1)
  have ht := observableEntropy_le_log_on_superset Finset.univ Finset.univ
    (S.wordWeight (n := n)) (tagWord tag) (fun _ _ => Finset.mem_univ _)
    (fun w _ => (S.wordWeight_pos w).le) (S.wordWeight_sum n)
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow] at ht
  rw [S.map_entropy_as_observation] at he
  unfold conditionalEntropy
  linarith

noncomputable def entropyLoss (S : System α) (tag : α → β) {n : ℕ}
    (w : Fin n → α) (ρ : ℝ) : ℝ :=
  ((law S tag w).shannonEntropy-(law S tag w).gridEntropy ρ)*Real.log 2

omit [Fintype β] in
theorem entropyLoss_nonneg (S : System α) (tag : α → β) {n : ℕ}
    (w : Fin n → α) (ρ : ℝ) : 0 ≤ entropyLoss S tag w ρ := by
  classical
  let ν := law S tag w
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := observableEntropy_le ν.support ν.prob (fun x => ⌊x/ρ⌋)
    (fun x hx => (ν.prob_pos x hx).le)
  dsimp only [entropyLoss,Law.shannonEntropy,Law.gridEntropy]
  have he : (entropy ν.support ν.prob/Real.log 2-
        observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋)/Real.log 2)*Real.log 2=
      entropy ν.support ν.prob-observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋) := by
    field_simp
  exact he ▸ sub_nonneg.mpr h

omit [Fintype β] in
theorem entropyLoss_le (S : System α) (tag : α → β) {n : ℕ}
    (w : Fin n → α) (ρ : ℝ) :
    entropyLoss S tag w ρ ≤ (n : ℝ)*Real.log (Fintype.card α) := by
  classical
  let p := fun v : Fin n → α => S.wordWeight v / FiniteCondition.mass S.wordWeight (tagWord tag) w
  let s := fiber (tagWord tag) w
  have hp : ∀ v ∈ s, 0 ≤ p v := fun v _ =>
    (div_pos (S.wordWeight_pos v) (mass_pos S.wordWeight S.wordWeight_pos (tagWord tag) w)).le
  have hp1 : ∑ v ∈ s, p v=1 := fiber_normalized_sum S.wordWeight S.wordWeight_pos (tagWord tag) w
  have hle := (observableEntropy_le s p (fun v => (S.completeMap v).2) hp).trans
    (entropy_le_log_card s p hp hp1)
  have hs : (0 : ℝ)<s.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨w,by simp [s,fiber]⟩
  have ht : (s.card : ℝ) ≤ (Fintype.card α : ℝ)^n := by
    have hc := Finset.card_le_card (Finset.subset_univ s)
    simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using
      (show (s.card : ℝ) ≤ (Finset.card (Finset.univ : Finset (Fin n → α)) : ℝ) by exact_mod_cast hc)
  have hlog := Real.log_le_log hs ht
  rw [Real.log_pow] at hlog
  let f := fun v : Fin n → α => ⌊(S.completeMap v).2/ρ⌋
  have hm : ∀ b, 0 ≤ FiniteEntropy.mass s p f b := FiniteEntropy.mass_nonneg s p f hp
  have hnon : 0 ≤ observableEntropy s p f := by
    apply FiniteEntropy.entropy_nonneg _ _ (fun b _ => hm b)
    intro b hb
    exact (Finset.single_le_sum (fun c _ => hm c) hb).trans_eq
      ((FiniteEntropy.mass_sum s p f).trans hp1)
  dsimp only [entropyLoss,law,FiniteCondition.law]
  rw [Law.ofObservable_entropy,Law.ofObservable_gridEntropy]
  have hl : Real.log 2≠0 := (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne'
  change (observableEntropy s p (fun v => (S.completeMap v).2)/Real.log 2-
    observableEntropy s p (fun v => ⌊(S.completeMap v).2/ρ⌋)/Real.log 2)*Real.log 2 ≤ _
  field_simp
  linarith

theorem expected_entropyLoss_lower (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    S.walkEntropy n*Real.log 2-(n : ℝ)*Real.log (Fintype.card β)-grid μ ρ 0-Real.log 2 ≤
      ∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w ρ := by
  have he := expected_entropy_lower S tag hr n
  have hg := expected_grid_upper S tag hr μ hμ hc n hρ
  have hid : (∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w ρ)=
      (∑ w : Fin n → α, S.wordWeight w*(law S tag w).shannonEntropy)*Real.log 2-
      (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 := by
    simp only [entropyLoss,mul_sub,sub_mul,← mul_assoc,Finset.sum_sub_distrib,Finset.sum_mul]
  rw [hid]
  linarith

end EntropyRateDimension.Typed

end OAI

import OAI.MeasureTheory.SelfSimilar.TypedLaw

namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

noncomputable def scaledTail (S : System α) (tag : α → β) (μ : Measure ℝ)
    (a : ℝ) {n : ℕ} (w : Fin n → α) : Measure ℝ :=
  (tail S tag μ w).map (fun x => a*x)

instance scaledTail_probability (S : System α) (tag : α → β) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (a : ℝ) {n : ℕ} (w : Fin n → α) :
    IsProbabilityMeasure (scaledTail S tag μ a w) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_const.mul measurable_id).aemeasurable).2 inferInstance

theorem scaledTail_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : CompactlyCarried μ) (a : ℝ) {n : ℕ} (w : Fin n → α) :
    CompactlyCarried (scaledTail S tag μ a w) := by
  simpa only [scaledTail,add_zero] using (tail_compact S tag μ hμ w).map_affine a 0

theorem scaledTail_mean (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : S.SelfSimilar μ) (a : ℝ) (n : ℕ) :
    (∑ w : Fin n → α, ENNReal.ofReal (S.wordWeight w) • scaledTail S tag μ a w)=
      μ.map (fun x => a*x) := by
  calc
    _ = (∑ w : Fin n → α, ENNReal.ofReal (S.wordWeight w) • tail S tag μ w).map
        (fun x => a*x) := by
      rw [Measure.map_finset_sum (show AEMeasurable (fun x : ℝ => a*x) _ from
        (measurable_const.mul measurable_id).aemeasurable)]
      simp only [Measure.map_smul (f := fun x : ℝ => a*x) _
        (measurable_const.mul measurable_id).aemeasurable,scaledTail]
    _ = _ := by rw [tail_mean S tag μ hμ n]

theorem scaled_tail_convolution (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (a : ℝ) {n : ℕ} (w : Fin n → α) :
    scaledTail S tag μ a w =
      finiteConv (law S tag w) a (μ.map (fun x => (a*(S.completeMap w).1)*x)) := by
  classical
  have he := law_smul_sum S.wordWeight (fun v : Fin n → α => S.wordWeight_pos v)
    (tagWord tag) w (fun v => (S.completeMap v).2)
    (fun x => shiftLaw (μ.map (fun y => (a*(S.completeMap w).1)*y)) (a*x))
  change finiteConv (law S tag w) a (μ.map (fun x => (a*(S.completeMap w).1)*x)) = _ at he
  rw [he]
  unfold scaledTail tail
  rw [Measure.map_finset_sum (show AEMeasurable (fun x : ℝ => a*x) _ from
    (measurable_const.mul measurable_id).aemeasurable)]
  simp only [Measure.map_smul (f := fun x : ℝ => a*x) _
    (measurable_const.mul measurable_id).aemeasurable]
  apply Finset.sum_congr rfl
  intro v _
  rw [← prob_as_posterior]
  by_cases h : prob S tag w v=0
  · simp only [h,ENNReal.ofReal_zero,zero_smul]
  · rw [shiftLaw,Measure.map_map (show Measurable (fun x : ℝ => a*x) from
        measurable_const.mul measurable_id) (S.wordMap_measurable v),
      Measure.map_map (show Measurable (fun x : ℝ => x+a*(S.completeMap v).2) from
        measurable_id.add_const _) (show Measurable
        (fun x : ℝ => (a*(S.completeMap w).1)*x) from measurable_const.mul measurable_id)]
    congr 2
    funext x
    simp only [Function.comp_apply,System.wordMap,prob_slope S tag hr h]
    ring

theorem scaledTail_append (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (a : ℝ) {m n : ℕ} (w : Fin m → α) (z : Fin n → α) :
    scaledTail S tag μ a (Fin.append w z)=
      finiteConv (law S tag w) a (scaledTail S tag μ (a*(S.completeMap w).1) z) := by
  change (tail S tag μ (Fin.append w z)).map (fun x => a*x)=_
  rw [tail_append]
  exact scaled_tail_convolution S tag hr _ a w

theorem scaledTail_window_drop (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (a : ℝ) {m n : ℕ} (w : Fin m → α) (z : Fin n → α)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    window (scaledTail S tag μ (a*(S.completeMap w).1) z) s (N*s) ≤
      window (scaledTail S tag μ a (Fin.append w z)) s (N*s) := by
  rw [scaledTail_append S tag hr]
  exact finiteConv_window_mono _ _ _ (scaledTail_compact S tag μ hμ _ z) hs hN

end EntropyRateDimension.Typed

end OAI

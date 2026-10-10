import OAI.MeasureTheory.SelfSimilar.PairGain

namespace OAI

universe uι uα uβ uγ uM

namespace EntropyRateDimension.FiniteCondition
open scoped BigOperators ENNReal
open MeasureTheory

theorem mass_pi {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype α] [Fintype γ] [DecidableEq γ] [DecidableEq β]
    (p : α → ℝ) (tag : α → β) (w : γ → α) :
    mass (fun v : γ → α => ∏ j, p (v j)) (fun v j => tag (v j)) w =
      ∏ j, mass p tag (w j) := by
  classical
  simp only [mass,fiber,Finset.sum_filter]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : (fun j => tag (v j))=(fun j => tag (w j))
  · simp only [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro j _
    rw [ite_eq_left (congrFun h j)]
  · rw [ite_eq_right h]
    symm
    obtain ⟨j,hj⟩ : ∃ j, tag (v j)≠tag (w j) := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem posterior_pi {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype α] [Fintype γ] [DecidableEq γ] [DecidableEq β]
    (p : α → ℝ) (tag : α → β) (w v : γ → α) :
    posterior (fun u : γ → α => ∏ j, p (u j)) (fun u j => tag (u j)) w v =
      ∏ j, posterior p tag (w j) (v j) := by
  classical
  rw [posterior,mass_pi]
  by_cases h : (fun j => tag (v j))=(fun j => tag (w j))
  · rw [ite_eq_left h,← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [posterior,ite_eq_left (congrFun h j)]
  · rw [ite_eq_right h]
    symm
    obtain ⟨j,hj⟩ : ∃ j, tag (v j)≠tag (w j) := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [posterior,ite_eq_right hj])

end EntropyRateDimension.FiniteCondition

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem sum_words_append {M : Type uM} [AddCommMonoid M] (m n : ℕ)
    (f : (Fin (m+n) → ι) → M) :
    (∑ w, f w)=∑ u : Fin m → ι, ∑ v : Fin n → ι, f (Fin.append u v) := by
  classical
  rw [← (Fin.appendEquiv m n).sum_comp f,Fintype.sum_prod_type]
  rfl

theorem completeMap_append (S : System ι) {m n : ℕ} (u : Fin m → ι) (v : Fin n → ι) :
    S.completeMap (Fin.append u v)=
      ((S.completeMap u).1*(S.completeMap v).1,
        (S.completeMap u).1*(S.completeMap v).2+(S.completeMap u).2) := by
  simp only [completeMap,List.ofFn_fin_append,wordAffine_append]

theorem wordWeight_append (S : System ι) {m n : ℕ} (u : Fin m → ι) (v : Fin n → ι) :
    S.wordWeight (Fin.append u v)=S.wordWeight u*S.wordWeight v := by
  simp only [wordWeight,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

theorem wordMap_append (S : System ι) {m n : ℕ} (u : Fin m → ι) (v : Fin n → ι) :
    S.wordMap (Fin.append u v)=S.wordMap u ∘ S.wordMap v := by
  funext x
  simp only [wordMap,completeMap_append,Function.comp_apply]
  ring

end EntropyRateDimension.System

namespace EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

abbrev tagWord (tag : α → β) {n : ℕ} (w : Fin n → α) : Fin n → β := fun j => tag (w j)

noncomputable def prob (S : System α) (tag : α → β) {n : ℕ} (w v : Fin n → α) : ℝ :=
  ∏ j, posterior S.weight tag (w j) (v j)

theorem prob_as_posterior (S : System α) (tag : α → β) {n : ℕ} (w v : Fin n → α) :
    prob S tag w v=posterior S.wordWeight (tagWord tag) w v :=
  (posterior_pi S.weight tag w v).symm

theorem prob_nonneg (S : System α) (tag : α → β) {n : ℕ} (w v : Fin n → α) :
    0 ≤ prob S tag w v :=
  Finset.prod_nonneg (fun j _ => posterior_nonneg S.weight S.weight_pos tag (w j) (v j))

theorem prob_sum (S : System α) (tag : α → β) {n : ℕ} (w : Fin n → α) :
    ∑ v, prob S tag w v=1 := by
  classical
  simp only [prob,← Fintype.prod_sum,posterior_sum S.weight S.weight_pos,Finset.prod_const_one]

theorem prob_append (S : System α) (tag : α → β) {m n : ℕ}
    (w u : Fin m → α) (z v : Fin n → α) :
    prob S tag (Fin.append w z) (Fin.append u v)=prob S tag w u*prob S tag z v := by
  simp only [prob,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

theorem prob_slope (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} {w v : Fin n → α} (h : prob S tag w v≠0) :
    (S.completeMap v).1=(S.completeMap w).1 := by
  rw [S.completeMap_slope,S.completeMap_slope]
  apply Finset.prod_congr rfl
  intro j hj
  apply hr
  by_contra ht
  apply h
  apply Finset.prod_eq_zero hj
  exact ite_eq_right ht

noncomputable def law (S : System α) (tag : α → β) {n : ℕ} (w : Fin n → α) : Law :=
  FiniteCondition.law S.wordWeight (fun v => S.wordWeight_pos v) (tagWord tag) w
    (fun v => (S.completeMap v).2)

noncomputable def tail (S : System α) (tag : α → β) (μ : Measure ℝ)
    {n : ℕ} (w : Fin n → α) : Measure ℝ :=
  ∑ v, ENNReal.ofReal (prob S tag w v) • μ.map (S.wordMap v)

instance tail_probability (S : System α) (tag : α → β) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {n : ℕ} (w : Fin n → α) : IsProbabilityMeasure (tail S tag μ w) := by
  have h (v : Fin n → α) : IsProbabilityMeasure (μ.map (S.wordMap v)) :=
    (Measure.isProbabilityMeasure_map_iff (S.wordMap_measurable v).aemeasurable).2 inferInstance
  let := h
  exact MeasureEntropy.mixture_probability (fun v => μ.map (S.wordMap v)) (prob S tag w)
    (prob_nonneg S tag w) (prob_sum S tag w)

theorem tail_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : MeasureEntropy.CompactlyCarried μ) {n : ℕ} (w : Fin n → α) :
    MeasureEntropy.CompactlyCarried (tail S tag μ w) := by
  apply MeasureEntropy.CompactlyCarried.mixture
  intro v
  exact hμ.map_affine _ _

theorem tail_mean (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : S.SelfSimilar μ) (n : ℕ) :
    (∑ w : Fin n → α, ENNReal.ofReal (S.wordWeight w) • tail S tag μ w)=μ := by
  simp only [tail,prob_as_posterior]
  rw [posterior_smul_uncondition S.wordWeight (fun v => S.wordWeight_pos v)]
  exact (S.selfSimilar_words μ hμ n).symm

theorem tail_append (S : System α) (tag : α → β) (μ : Measure ℝ)
    {m n : ℕ} (w : Fin m → α) (z : Fin n → α) :
    tail S tag μ (Fin.append w z)=tail S tag (tail S tag μ z) w := by
  classical
  rw [tail,System.sum_words_append]
  simp only [tail]
  apply Finset.sum_congr rfl
  intro u _
  rw [Measure.map_finset_sum (S.wordMap_measurable u).aemeasurable,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [prob_append,ENNReal.ofReal_mul (prob_nonneg S tag w u),
    Measure.map_smul _ (S.wordMap_measurable u).aemeasurable,smul_smul,
    Measure.map_map (S.wordMap_measurable u) (S.wordMap_measurable v),S.wordMap_append]

end EntropyRateDimension.Typed

end OAI

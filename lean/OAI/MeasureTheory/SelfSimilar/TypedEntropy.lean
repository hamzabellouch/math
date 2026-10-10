import OAI.MeasureTheory.SelfSimilar.KernelEntropy

namespace OAI

universe uα uβ uγ

namespace EntropyRateDimension.FiniteCondition
open scoped BigOperators
open FiniteEntropy

theorem entropy_expectation {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (f : α → γ) :
    (∑ a, p a*observableEntropy (fiber tag a) (fun v => p v/mass p tag a) f)=
      conditionalEntropy Finset.univ p f tag := by
  classical
  rw [conditionalEntropy_eq_sum _ _ _ _ (fun a _ => (hp a).le)]
  symm
  convert FiniteEntropy.sum_mass_mul Finset.univ (Finset.univ.image tag) p tag
    (fun c => observableEntropy (Finset.univ.filter (fun a => tag a=c))
      (fun a => p a/FiniteEntropy.mass Finset.univ p tag c) f)
    (fun a ha => Finset.mem_image_of_mem tag ha) using 1
  rfl

end EntropyRateDimension.FiniteCondition

namespace EntropyRateDimension.FiniteEntropy
open scoped BigOperators
open MeasureEntropy

theorem shifted_grid_compare {α : Type uα} (s : Finset α) (p f : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a=1)
    {ρ : ℝ} (hρ : 0 < ρ) (u v : ℝ) :
    observableEntropy s p (fun a => label ρ u (f a)) ≤
      observableEntropy s p (fun a => label ρ v (f a))+Real.log 2 := by
  classical
  let g := fun a => label ρ v (f a)
  let r := fun a => relativeLabel ρ ρ u v (f a)
  have hr : ∀ a ∈ s, r a ∈ Finset.Icc (0 : ℤ) 1 := by
    intro a _
    simpa only [div_self hρ.ne',Int.ceil_one] using relativeLabel_mem hρ hρ u v (f a)
  have he := observableEntropy_le_of_fibers s p (fun a => label ρ u (f a))
    (fun a => (g a,r a)) hp (by
      intro a _ b _ hab
      obtain ⟨h1,h2⟩ := Prod.mk.inj hab
      dsimp [r,relativeLabel] at h2
      change label ρ v (f a)=label ρ v (f b) at h1
      rw [h1] at h2
      linarith)
  have hh := observableEntropy_pair_le s p g r hp hp1
  have hle := observableEntropy_le_log_on_superset s (Finset.Icc (0 : ℤ) 1) p r hr hp hp1
  norm_num at hle
  change observableEntropy s p r ≤ Real.log 2 at hle
  change _ ≤ observableEntropy s p g+Real.log 2
  linarith

end EntropyRateDimension.FiniteEntropy

namespace EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition FiniteEntropy MeasureEntropy
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem expected_grid_comparison (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (y : ℝ) :
    (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 ≤
      observableEntropy Finset.univ (S.wordWeight (n := n)) (fun v => ⌊S.wordMap v y/ρ⌋)+Real.log 2 := by
  classical
  let p := S.wordWeight (n := n)
  let t := tagWord tag (n := n)
  have hp : ∀ v, 0 < p v := S.wordWeight_pos
  have hlocal (w : Fin n → α) :
      (law S tag w).gridEntropy ρ*Real.log 2 ≤
        observableEntropy (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
          (fun v => ⌊S.wordMap v y/ρ⌋)+Real.log 2 := by
    have hc := shifted_grid_compare (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
      (fun v => (S.completeMap v).2)
      (fun v _ => (div_pos (hp v) (mass_pos p hp t w)).le) (fiber_normalized_sum p hp t w)
      hρ 0 ((S.completeMap w).1*y/ρ)
    have hobs : observableEntropy (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
        (fun v => label ρ ((S.completeMap w).1*y/ρ) (S.completeMap v).2) =
        observableEntropy (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
          (fun v => ⌊S.wordMap v y/ρ⌋) := by
      apply observableEntropy_congr _ _ _ _ _ (fun _ _ => rfl)
      intro v hv
      have hv' : t v=t w := (Finset.mem_filter.mp hv).2
      have hsl : (S.completeMap v).1=(S.completeMap w).1 := by
        rw [S.completeMap_slope,S.completeMap_slope]
        exact Finset.prod_congr rfl (fun j _ => hr _ _ (congrFun hv' j))
      unfold label System.wordMap
      rw [hsl]
      congr 1
      ring
    rw [hobs] at hc
    simpa only [law,FiniteCondition.law,Law.ofObservable_gridEntropy,
      div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne',label,add_zero] using hc
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hlocal w) (S.wordWeight_pos w).le)
  simp only [mul_add,Finset.sum_add_distrib,← mul_assoc,← Finset.sum_mul,S.wordWeight_sum,one_mul] at hsum
  rw [entropy_expectation p hp t] at hsum
  have hh := conditionalEntropy_le Finset.univ p (fun v => ⌊S.wordMap v y/ρ⌋) t
    (fun w _ => (hp w).le) (S.wordWeight_sum n)
  exact hsum.trans (by linarith)

theorem word_map_ae (S : System α) (μ : Measure ℝ) (hμ : S.SelfSimilar μ)
    {n : ℕ} (w : Fin n → α) {P : ℝ → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂μ.map (S.wordMap w), P x := by
  classical
  rw [ae_iff] at hP ⊢
  have hle : ENNReal.ofReal (S.wordWeight w) • μ.map (S.wordMap w) ≤ μ := by
    conv_rhs => rw [S.selfSimilar_words μ hμ n]
    exact Finset.single_le_sum (fun v (_ : v ∈ Finset.univ) =>
      (bot_le : (0 : Measure ℝ) ≤ ENNReal.ofReal (S.wordWeight v) • μ.map (S.wordMap v)))
      (Finset.mem_univ w)
  have hz : ENNReal.ofReal (S.wordWeight w)*(μ.map (S.wordMap w)) {x | ¬P x}=0 := by
    apply le_antisymm _ (zero_le : (0 : ℝ≥0∞) ≤ _)
    simpa only [Measure.smul_apply,smul_eq_mul,hP] using hle {x | ¬P x}
  exact (mul_eq_zero.mp hz).resolve_left (ENNReal.ofReal_ne_zero_iff.mpr (S.wordWeight_pos w))

theorem expected_grid_upper (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 ≤
      grid μ ρ 0+Real.log 2 := by
  classical
  obtain ⟨B,_,hB⟩ := hc
  let s := Finset.Icc ⌊-B/ρ+(0 : ℝ)⌋ ⌊B/ρ+(0 : ℝ)⌋
  have hs (w : Fin n → α) : ∀ᵐ y ∂μ, label ρ 0 (S.wordMap w y) ∈ s := by
    apply (ae_map_iff (S.wordMap_measurable w).aemeasurable
      ((label_measurable ρ 0) s.finite_toSet.measurableSet)).mp
    exact word_map_ae S μ hμ w (label_ae_finite μ hρ hB)
  have hj := random_observation_entropy μ μ S.wordWeight (fun w => (S.wordWeight_pos w).le)
    (S.wordWeight_sum n) S.wordMap S.wordMap_measurable (S.selfSimilar_words μ hμ n)
    (label ρ 0) (label_measurable ρ 0) s hs
  have hi := random_observation_integrable μ S.wordWeight (fun w => (S.wordWeight_pos w).le)
    (S.wordWeight_sum n) (fun w y => label ρ 0 (S.wordMap w y))
    (fun w => (label_measurable ρ 0).comp (S.wordMap_measurable w)) s hs
  have hpoint := integral_mono (integrable_const
    ((∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2))
    (hi.add (integrable_const (Real.log 2)))
    (fun y => by
      change _ ≤ observableEntropy Finset.univ S.wordWeight
        (fun v => label ρ 0 (S.wordMap v y))+Real.log 2
      simpa only [label,add_zero] using expected_grid_comparison S tag hr hρ y)
  change (∫ _ : ℝ, (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 ∂μ) ≤
    (∫ y, observableEntropy Finset.univ S.wordWeight (fun v => label ρ 0 (S.wordMap v y))+Real.log 2 ∂μ) at hpoint
  rw [integral_add hi (integrable_const _)] at hpoint
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hpoint
  exact hpoint.trans (by simpa only [grid,add_comm] using add_le_add_right hj (Real.log 2))

end EntropyRateDimension.Typed

end OAI

import OAI.Probability.CriticalPercolation.ProductMeasure.ProductConditioning

namespace OAI

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E B : Type*}

lemma measurable_block_of_dependsOn {A : Type*} [MeasurableSpace A]
    {f : Set E → A} (hf : Measurable f) (S : Set E) (hdep : DependsOn f S) :
    @Measurable (Set E) A (blockSigma S) inferInstance f := by
  have hm := hf.comp (measurable_forceOn_block Sᶜ (∅ : Set E))
  rw [compl_compl] at hm
  convert hm using 1
  funext ω
  apply hdep
  intro e he
  simp only [forceOn, Set.mem_compl_iff, ite_eq_right (not_not.mpr he),
    Set.mem_empty_iff_false]
  rfl

lemma lintegral_indicator_fresh (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (hdep : DependsOn (fun ω => ω ∈ A) S)
    (g : Set E → ℝ≥0∞) (hg : Measurable g) (hgdep : DependsOn g Sᶜ) :
    (∫⁻ ω, A.indicator g ω ∂law q) = law q A * ∫⁻ ω, g ω ∂law q := by
  have hAb : MeasurableSet[blockSigma S] A := by
    have hm := hA.preimage (measurable_forceOn_block Sᶜ (∅ : Set E))
    rw [compl_compl] at hm
    convert hm using 1
    ext ω
    apply Iff.of_eq
    apply hdep
    intro e he
    simp only [forceOn, Set.mem_compl_iff, ite_eq_right (not_not.mpr he)]
    rfl
  have hgb := measurable_block_of_dependsOn hg Sᶜ hgdep
  have hi := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (blockSigma_le S) (blockSigma_le Sᶜ)
    (independent_blocks q S)
    ((measurable_const : @Measurable (Set E) ℝ≥0∞ (blockSigma S) inferInstance
      (fun _ => 1)).indicator hAb) hgb
  have heq : (fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) ω * g ω) = A.indicator g := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  have hone := lintegral_indicator_const (μ := law q) hA (1 : ℝ≥0∞)
  simp only [one_mul] at hone
  rw [heq, hone] at hi
  exact hi

theorem lintegral_countable_exposure [Countable B] [MeasurableSpace B]
    [MeasurableSingletonClass B] (q : E → unitInterval) (exposed : Set E → B)
    (hm : Measurable exposed) (block : B → Set E)
    (hd : ∀ b, DependsOn (fun ω => exposed ω = b) (block b))
    (g : B → Set E → ℝ≥0∞) (hg : ∀ b, Measurable (g b))
    (hgd : ∀ b, DependsOn (g b) (block b)ᶜ) :
    (∫⁻ ω, g (exposed ω) ω ∂law q) =
      ∑' b, law q {ω | exposed ω = b} * ∫⁻ η, g b η ∂law q := by
  have hA (b : B) : MeasurableSet {ω | exposed ω = b} :=
    hm (MeasurableSet.singleton b)
  have heq (ω : Set E) : g (exposed ω) ω =
      ∑' b, ({ω | exposed ω = b} : Set (Set E)).indicator (g b) ω := by
    simp [Set.indicator, eq_comm]
  simp_rw [heq]
  rw [lintegral_tsum (fun b => ((hg b).indicator (hA b)).aemeasurable)]
  apply tsum_congr
  intro b
  exact lintegral_indicator_fresh q (block b) _ (hA b) (hd b) (g b) (hg b) (hgd b)

end CriticalPercolation.BernoulliProduct

end

end OAI

import Mathlib
import OAI.Probability.SphericalField.Heat.Backward

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]
lemma gaussianBackward_label_parameter_bound {I : Type*} {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (l : List (I×ℝ)) (a b : I → ℝ) {S : ℝ}
    (ha : ∀ c ∈ l, a c.1 ∈ Icc (0:ℝ) 1) (hb : ∀ c ∈ l, b c.1 ∈ Icc (0:ℝ) 1)
    (hσ : ∀ c ∈ l, c.2 ∈ Icc (0:ℝ) S) : ∀ x,
    |gaussianBackward μ (l.map fun c => (a c.1,c.2)) f x-
      gaussianBackward μ (l.map fun c => (b c.1,c.2)) f x| ≤
      gaussianEntropicParamConstant μ L S*(l.map fun c => c.2^2*|a c.1-b c.1|).sum := by
  induction l with
  | nil => intro x; simp [gaussianBackward]
  | cons c l ih =>
    have ha' := fun d hd => ha d (List.mem_cons_of_mem c hd)
    have hb' := fun d hd => hb d (List.mem_cons_of_mem c hd)
    have hσ' := fun d hd => hσ d (List.mem_cons_of_mem c hd)
    have hla : LipschitzWith L (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact (ha' e he).1
    have hlb : LipschitzWith L (gaussianBackward μ (l.map fun d => (b d.1,d.2)) f) := by
      apply gaussianBackward_lipschitz μ hf
      intro d hd
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hd
      exact (hb' e he).1
    intro x
    simp only [List.map_cons,List.sum_cons,gaussianBackward]
    have H1 := gaussianEntropic_parameter_bound μ hla (ha c List.mem_cons_self)
      (hb c List.mem_cons_self) (hσ c List.mem_cons_self).1 (hσ c List.mem_cons_self).2 x
    have H2 := entropicMean_bounded_difference μ
      (fun t => gaussian_integrable_exp_lipschitz μ hla t c.2 x)
      (fun t => gaussian_integrable_exp_lipschitz μ hlb t c.2 x) (hb c List.mem_cons_self).1
      (ae_of_all _ fun y => ih ha' hb' hσ' (x+c.2 • y))
    have HT := abs_sub_le (gaussianEntropic μ (a c.1) c.2 (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) x)
      (gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) x)
      (gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (b d.1,d.2)) f) x)
    dsimp [entropicMean] at H2
    change |gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (a d.1,d.2)) f) x-
      gaussianEntropic μ (b c.1) c.2 (gaussianBackward μ (l.map fun d => (b d.1,d.2)) f) x| ≤ _ at H2
    nlinarith

lemma gaussianBackward_ofFn_parameter_bound {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (N : ℕ) (a b σ : Fin N → ℝ) {S : ℝ}
    (ha : ∀ i, a i ∈ Icc (0:ℝ) 1) (hb : ∀ i, b i ∈ Icc (0:ℝ) 1)
    (hσ : ∀ i, σ i ∈ Icc (0:ℝ) S) (x : E) :
    |gaussianBackward μ (List.ofFn fun i => (a i,σ i)) f x-
      gaussianBackward μ (List.ofFn fun i => (b i,σ i)) f x| ≤
      gaussianEntropicParamConstant μ L S*(∑ i, (σ i)^2*|a i-b i|) := by
  have ha' : ∀ c ∈ List.ofFn (fun i => (i,σ i)), a c.1 ∈ Icc (0:ℝ) 1 := by
    intro c hc; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc; exact ha i
  have hb' : ∀ c ∈ List.ofFn (fun i => (i,σ i)), b c.1 ∈ Icc (0:ℝ) 1 := by
    intro c hc; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc; exact hb i
  have hσ' : ∀ c ∈ List.ofFn (fun i => (i,σ i)), c.2 ∈ Icc (0:ℝ) S := by
    intro c hc; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc; exact hσ i
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_def] using
    gaussianBackward_label_parameter_bound μ hf (List.ofFn fun i => (i,σ i)) a b ha' hb' hσ' x

end
end SphericalPerceptron
end
end

end OAI

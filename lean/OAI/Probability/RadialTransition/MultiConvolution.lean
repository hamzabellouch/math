import OAI.Probability.RadialTransition.ClusterWeights

namespace OAI

universe uX

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

section Multi
variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

lemma particleBase_emptyWeight (μ : Measure X) [SigmaFinite μ] (z : ℝ) :
    (∫⁻ x, emptyWeight (particleMultiset x) ∂particleBase μ z) = 1 := by
  have hm := measurable_particleObservable (emptyWeight (X := X)) measurable_emptyWeight 0
  simp only [zero_add] at hm
  rw [lintegral_particleBase μ z hm, tsum_eq_single 0]
  · simp [particleMultiset, emptyWeight, configurationMultiset_card]
  · intro n hn
    simp [particleMultiset, emptyWeight, configurationMultiset_card, hn]

def finClusterProduct : (n : ℕ) → (Fin n → Multiset X → ℝ≥0∞) → Multiset X → ℝ≥0∞
  | 0, _ => emptyWeight
  | n+1, W => clusterConvolution (W 0) (finClusterProduct n (fun i => W i.succ))

omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma measurable_finClusterProduct (n : ℕ) (W : Fin n → Multiset X → ℝ≥0∞)
    (hW : ∀ i, MeasurableConfiguration (W i)) : MeasurableConfiguration (finClusterProduct n W) := by
  induction n with
  | zero => exact measurable_emptyWeight
  | succ n ih => exact measurable_clusterConvolution (hW 0) (ih _ (fun i => hW i.succ))

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma finClusterProduct_ge (n : ℕ) (W : Fin n → Multiset X → ℝ≥0∞)
    (u : Fin n → Multiset X) : (∏ i, W i (u i)) ≤ finClusterProduct n W (∑ i, u i) := by
  induction n with
  | zero => simp [finClusterProduct, emptyWeight]
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    exact (mul_le_mul' le_rfl (ih (fun i => W i.succ) (fun i => u i.succ))).trans
      (clusterConvolution_add_ge (W 0) (finClusterProduct n (fun i => W i.succ)) _ _)

lemma particleBase_finClusterProduct (n : ℕ) (W : Fin n → Multiset X → ℝ≥0∞)
    (hW : ∀ i, MeasurableConfiguration (W i)) (μ : Measure X) [SigmaFinite μ] (z : ℝ) :
    (∫⁻ x, finClusterProduct n W (particleMultiset x) ∂particleBase μ z) =
      ∏ i, ∫⁻ x, W i (particleMultiset x) ∂particleBase μ z := by
  induction n with
  | zero => simpa only [finClusterProduct, Fin.prod_univ_zero] using particleBase_emptyWeight μ z
  | succ n ih =>
    rw [finClusterProduct, particleBase_convolution (hW 0)
      (measurable_finClusterProduct _ _ (fun i => hW i.succ)), ih _ (fun i => hW i.succ), Fin.prod_univ_succ]

variable {I : Type} [Fintype I]

def indexedClusterProduct (W : I → Multiset X → ℝ≥0∞) : Multiset X → ℝ≥0∞ :=
  finClusterProduct (Fintype.card I) (fun i => W ((Fintype.equivFin I).symm i))

omit [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma measurable_indexedClusterProduct (W : I → Multiset X → ℝ≥0∞)
    (hW : ∀ i, MeasurableConfiguration (W i)) : MeasurableConfiguration (indexedClusterProduct W) :=
  measurable_finClusterProduct _ _ (fun _i => hW _)

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma indexedClusterProduct_ge (W : I → Multiset X → ℝ≥0∞) (u : I → Multiset X) :
    (∏ i, W i (u i)) ≤ indexedClusterProduct W (∑ i, u i) := by
  have hh := finClusterProduct_ge (Fintype.card I)
    (fun i => W ((Fintype.equivFin I).symm i)) (fun i => u ((Fintype.equivFin I).symm i))
  rw [Equiv.sum_comp, Equiv.prod_comp (Fintype.equivFin I).symm (fun i => W i (u i))] at hh
  exact hh

lemma particleBase_indexedClusterProduct (W : I → Multiset X → ℝ≥0∞)
    (hW : ∀ i, MeasurableConfiguration (W i)) (μ : Measure X) [SigmaFinite μ] (z : ℝ) :
    (∫⁻ x, indexedClusterProduct W (particleMultiset x) ∂particleBase μ z) =
      ∏ i, ∫⁻ x, W i (particleMultiset x) ∂particleBase μ z := by
  rw [indexedClusterProduct, particleBase_finClusterProduct _ _ (fun _i => hW _)]
  exact Equiv.prod_comp (Fintype.equivFin I).symm (fun i => ∫⁻ x, W i (particleMultiset x) ∂particleBase μ z)

end Multi
end RadialTransition
end

end OAI

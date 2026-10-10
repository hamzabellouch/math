import OAI.Probability.RadialTransition.ClusterConvolution

namespace OAI

universe uX uY uIndex

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma clusterConvolution_add {X : Type uX} (F G : Multiset X → ℝ≥0∞) (s u : Multiset X) :
    clusterConvolution F G (s+u) =
      (s.antidiagonal.map (fun p => clusterConvolution (fun v => F (p.1+v)) (fun v => G (p.2+v)) u)).sum := by
  simp [clusterConvolution, Multiset.antidiagonal_add, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_map]

section Measurable
variable {X : Type uX} [MeasurableSpace X]

lemma measurable_configuration_subtype {F : Multiset X → ℝ≥0∞} (hF : MeasurableConfiguration F)
    (s : Multiset X) {ι : Type} [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    Measurable (fun x : ι → X => F (s+configurationMultiset (fun i : Subtype p => x i))) := by
  exact (hF s (Subtype p)).comp (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val))

lemma measurable_configuration_restrict {F : Multiset X → ℝ≥0∞} (hF : MeasurableConfiguration F)
    (s : Multiset X) {ι : Type} [Fintype ι] (T : Finset ι) :
    Measurable (fun x : ι → X => F (s+configurationMultiset (fun i : T => x i))) := by
  apply (hF s T).comp
  exact measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)

lemma measurable_multiset_sum {Y : Type uY} [MeasurableSpace Y] {ι : Type uIndex}
    (s : Multiset ι) (f : ι → Y → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x => (s.map (fun i => f i x)).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact measurable_add.comp ((hf a).prodMk ih)

lemma measurable_clusterConvolution {F G : Multiset X → ℝ≥0∞}
    (hF : MeasurableConfiguration F) (hG : MeasurableConfiguration G) :
    MeasurableConfiguration (clusterConvolution F G) := by
  classical
  intro s ι _
  simp_rw [clusterConvolution_add, clusterConvolution_configuration]
  apply measurable_multiset_sum
  intro p
  apply Finset.measurable_sum
  intro T _
  exact (measurable_configuration_subtype hF p.1 (fun i => i ∉ T)).mul
    (measurable_configuration_restrict hG p.2 T)

lemma configuration_integral_card (F : Multiset X → ℝ≥0∞) (μ : Measure X) [SigmaFinite μ]
    (ι : Type) [Fintype ι] :
    (∫⁻ x : ι → X, F (configurationMultiset x) ∂Measure.pi (fun _ => μ)) =
      ∫⁻ x : Fin (Fintype.card ι) → X, F (configurationMultiset x) ∂Measure.pi (fun _ => μ) := by
  exact functional_integral_equiv (fun _ι _ x => F (configurationMultiset x))
    (fun _ι _κ _ _ e x => congrArg F (configurationMultiset_equiv e x)) (Fintype.equivFin ι) (fun _ => μ)

lemma configuration_split_integral {F G : Multiset X → ℝ≥0∞}
    (hF : MeasurableConfiguration F) (hG : MeasurableConfiguration G)
    (μ : Measure X) [SigmaFinite μ] {ι : Type} [Fintype ι] [DecidableEq ι] (T : Finset ι) :
    (∫⁻ x : ι → X, F (configurationMultiset (fun i : {i // i ∉ T} => x i)) *
      G (configurationMultiset (fun i : T => x i)) ∂Measure.pi (fun _ => μ)) =
      (∫⁻ x : {i // i ∉ T} → X, F (configurationMultiset x) ∂Measure.pi (fun _ => μ))*
      (∫⁻ x : T → X, G (configurationMultiset x) ∂Measure.pi (fun _ => μ)) := by
  have hp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => μ) (fun i => i ∈ T)
  have hG0 : Measurable (fun x : T → X => G (configurationMultiset x)) := by
    simpa only [zero_add] using hG 0 T
  have hF0 : Measurable (fun x : {i // i ∉ T} → X => F (configurationMultiset x)) := by
    simpa only [zero_add] using hF 0 {i // i ∉ T}
  have hmeas : Measurable (fun p : (T → X) × ({i // i ∉ T} → X) =>
      G (configurationMultiset p.1)*F (configurationMultiset p.2)) := by
    exact (hG0.comp measurable_fst).mul (hF0.comp measurable_snd)
  have hh := hp.lintegral_comp hmeas
  simp only [MeasurableEquiv.piEquivPiSubtypeProd_apply] at hh
  have hi : Subtype.fintype (fun i : ι => i ∈ T) = Finset.Subtype.fintype T := Subsingleton.elim _ _
  rw [hi] at hh
  have hent := lintegral_prod_mul (μ := Measure.pi (fun _ : T => μ))
    (ν := Measure.pi (fun _ : {i // i ∉ T} => μ)) hG0.aemeasurable hF0.aemeasurable
  have hh := hh.trans hent
  simpa only [mul_comm] using hh

end Measurable
end RadialTransition
end

end OAI

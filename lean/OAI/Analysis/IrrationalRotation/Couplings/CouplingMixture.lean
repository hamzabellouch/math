import OAI.Analysis.IrrationalRotation.Model.CouplingMixture
import OAI.Analysis.IrrationalRotation.Model.CouplingMarginalBounds
import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Invariant233.CouplingMixture

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

lemma diagonal_fst (μ : Measure X) : (diagonal μ).fst = μ := by
  simpa [diagonal] using
    (Measure.fst_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id measurable_id)

lemma diagonal_snd (μ : Measure X) : (diagonal μ).snd = μ := by
  simpa [diagonal] using
    (Measure.snd_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id measurable_id)

instance diagonal_isProbabilityMeasure (μ : Measure X) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (diagonal μ) := by
  unfold diagonal
  infer_instance

lemma fst_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).fst = ∑ i ∈ s, (μ i).fst := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma snd_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).snd = ∑ i ∈ s, (μ i).snd := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma mixture_fst (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).fst = q • μ + ∑ i, p i • u i := by
  unfold mixture
  rw [Measure.fst_add, fst_finsetSum]
  simp only [Measure.fst, Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_fst_prod, measure_univ, one_smul]
  rw [← Measure.fst, diagonal_fst]

lemma mixture_snd (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).snd = q • μ + ∑ i, p i • v i := by
  unfold mixture
  rw [Measure.snd_add, snd_finsetSum]
  simp only [Measure.snd, Measure.map_smul _ measurable_snd.aemeasurable,
    Measure.map_snd_prod, measure_univ, one_smul]
  rw [← Measure.snd, diagonal_snd]

lemma mixture_isProbabilityMeasure (μ : Measure X) [IsProbabilityMeasure μ]
    (q : ℝ≥0∞) (p : I → ℝ≥0∞) (u v : I → Measure X)
    [∀ i, IsProbabilityMeasure (u i)] [∀ i, IsProbabilityMeasure (v i)]
    (htotal : q + ∑ i, p i = 1) : IsProbabilityMeasure (mixture μ q p u v) := by
  constructor
  simp only [mixture, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one, Measure.finsetSum_apply]
  simpa using htotal

lemma diagonal_ae {μ : Measure X} {R : X → X → Prop}
    (hR : MeasurableSet {z : X × X | R z.1 z.2}) (href : ∀ x, R x x) :
    ∀ᵐ z ∂diagonal μ, R z.1 z.2 := by
  unfold diagonal
  apply (ae_map_iff (show Measurable (fun x : X => (x, x)) from
    measurable_id.prodMk measurable_id).aemeasurable hR).2
  exact Filter.Eventually.of_forall href

lemma mixture_ae {μ : Measure X} {q : ℝ≥0∞} {p : I → ℝ≥0∞}
    {u v : I → Measure X} {P : X × X → Prop}
    (hdiag : ∀ᵐ z ∂diagonal μ, P z)
    (hcomp : ∀ i, ∀ᵐ z ∂(u i).prod (v i), P z) :
    ∀ᵐ z ∂mixture μ q p u v, P z := by
  rw [mixture, ae_add_measure_iff, ae_finsetSum_measure_iff]
  exact ⟨Measure.ae_smul_measure hdiag q, fun i _ => Measure.ae_smul_measure (hcomp i) (p i)⟩

lemma withDensity_finite_mixture (μ : Measure X) (q : ℝ≥0∞)
    (p : I → ℝ≥0∞) (g : I → X → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    μ.withDensity (fun x => q + ∑ i, p i * g i x) =
      q • μ + ∑ i, p i • μ.withDensity (g i) := by
  classical
  have hsum : μ.withDensity (fun x => ∑ i, p i * g i x) =
      ∑ i, p i • μ.withDensity (g i) := by
    have hfin : ∀ s : Finset I, μ.withDensity (fun x => ∑ i ∈ s, p i * g i x) =
        ∑ i ∈ s, p i • μ.withDensity (g i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [show (fun x => p a * g a x + ∑ i ∈ s, p i * g i x) =
          (fun x => p a * g a x) + (fun x => ∑ i ∈ s, p i * g i x) from rfl,
          withDensity_add_left (show Measurable (fun x => p a * g a x) from measurable_const.mul (hg a)), ih]
        congr 1
        exact withDensity_smul (p a) (hg a)
    exact hfin Finset.univ
  rw [show (fun x => q + ∑ i, p i * g i x) =
    (fun _ => q) + (fun x => ∑ i, p i * g i x) from rfl,
    withDensity_add_left measurable_const, withDensity_const, hsum]

lemma intervalLaw_isProbabilityMeasure {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (intervalLaw a b) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)
  · rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top

lemma intervalLaw_ae_mem (a b : ℝ) : ∀ᵐ x ∂intervalLaw a b, x ∈ Ico a b :=
  ae_cond_mem measurableSet_Ico

lemma intervalLaw_pair_ordered {a b c d : ℝ} (hbc : b ≤ c) :
    ∀ᵐ z ∂(intervalLaw a b).prod (intervalLaw c d), z.1 ≤ z.2 := by
  have : IsZeroOrProbabilityMeasure (intervalLaw a b) := inferInstanceAs
    (IsZeroOrProbabilityMeasure (volume[|Ico a b]))
  have : IsZeroOrProbabilityMeasure (intervalLaw c d) := inferInstanceAs
    (IsZeroOrProbabilityMeasure (volume[|Ico c d]))
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_fst measurable_snd)]
  filter_upwards [intervalLaw_ae_mem a b] with x hx
  filter_upwards [intervalLaw_ae_mem c d] with y hy
  exact hx.2.le.trans (hbc.trans hy.1)

lemma map_finsetSum {A B J : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (s : Finset J) (μ : J → Measure A) {f : A → B} (hf : Measurable f) :
    (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, Measure.map_add _ _ hf, ih]

omit [Fintype I] in
lemma map_snd_label [MeasurableSpace (Option I)] (ν : Measure (X × X))
    (l : Option I) : (ν.map (fun z => (l, z))).map Prod.snd = ν := by
  rw [Measure.map_map measurable_snd (show Measurable (fun z : X × X => (l, z)) from
    measurable_const.prodMk measurable_id)]
  exact Measure.map_id

omit [Fintype I] in
lemma map_label_event [DecidableEq I] [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (ν : Measure (X × X)) (l j : Option I) :
    ν.map (fun z => (l, z)) {z | z.1 = j} = if l = j then ν Set.univ else 0 := by
  classical
  have hs : MeasurableSet {z : Option I × (X × X) | z.1 = j} :=
    measurable_fst (measurableSet_singleton j)
  rw [Measure.map_apply (show Measurable (fun z : X × X => (l, z)) from
    measurable_const.prodMk measurable_id) hs]
  by_cases h : l = j <;> simp [h]

lemma labelledMixture_map_snd [MeasurableSpace (Option I)]
    (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞) (u v : I → Measure X) :
    (labelledMixture μ q p u v).map Prod.snd = mixture μ q p u v := by
  unfold labelledMixture mixture
  rw [Measure.map_add _ _ measurable_snd, map_finsetSum _ _ measurable_snd]
  simp only [Measure.map_smul _ measurable_snd.aemeasurable, map_snd_label]

lemma labelledMixture_isProbabilityMeasure [MeasurableSpace (Option I)]
    (μ : Measure X) [IsProbabilityMeasure μ] (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)] (htotal : q + ∑ i, p i = 1) :
    IsProbabilityMeasure (labelledMixture μ q p u v) := by
  constructor
  have := mixture_isProbabilityMeasure μ q p u v htotal
  have h := congrArg (fun ν : Measure (X × X) => ν Set.univ)
    (labelledMixture_map_snd μ q p u v)
  simpa [Measure.map_apply measurable_snd MeasurableSet.univ] using h

lemma labelledMixture_none_mass [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (μ : Measure X) [IsProbabilityMeasure μ] (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) :
    labelledMixture μ q p u v {z | z.1 = none} = q := by
  classical
  simp only [labelledMixture, Measure.add_apply, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul, map_label_event]
  simp

lemma labelledMixture_some_mass [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)] (i : I) :
    labelledMixture μ q p u v {z | z.1 = some i} = p i := by
  classical
  simp only [labelledMixture, Measure.add_apply, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul, map_label_event]
  simp

lemma cond_eq_withDensity_uniformDensity {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set X} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    μ[|s] = μ.withDensity (fun x =>
      ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) := by
  have hc : ENNReal.ofReal ((μ.real s)⁻¹) = (μ s)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hpos, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ s)]
  have hfun : (fun x => ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) =
      s.indicator (fun _ => (μ s)⁻¹) := by
    ext x
    by_cases hx : x ∈ s <;> simp [CouplingMarginalBounds.uniformDensity, hx, hc]
  rw [hfun, withDensity_indicator hs, withDensity_const]
  rfl

omit [MeasurableSpace X] in
lemma ofReal_mixture_density (q : ℝ) (p : I → ℝ) (g : I → X → ℝ)
    (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i) (hg : ∀ i x, 0 ≤ g i x) (x : X) :
    ENNReal.ofReal (q + ∑ i, p i * g i x) =
      ENNReal.ofReal q + ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (g i x) := by
  rw [ENNReal.ofReal_add hq (Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => ENNReal.ofReal_mul (hp i))

lemma mixture_fst_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hu : ∀ i, u i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).fst =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_fst]
  simp_rw [hu, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

lemma mixture_snd_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hv : ∀ i, v i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).snd =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_snd]
  simp_rw [hv, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

end Invariant233.CouplingMixture

end OAI

import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.UniformLaw
import OAI.Combinatorics.IndependentSets.Repetition.ScalarSampleInfluence
import OAI.Combinatorics.IndependentSets.Geometry.CoordinateDerivative

namespace OAI

namespace LargeIndependentSets.ProductAveraging
open MeasureTheory Set
open scoped BigOperators Classical

noncomputable def mix {ι α : Type*} (S : Finset ι) (p : (ι → α) × (ι → α)) : ι → α :=
  fun i => if i ∈ S then p.1 i else p.2 i

lemma mix_measurable {ι α : Type*} [Fintype ι] [MeasurableSpace α] (S : Finset ι) :
    Measurable (mix (α:=α) S) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ S
  · simpa only [mix, hi, ↓reduceIte, Function.comp_def] using (measurable_pi_apply i).comp measurable_fst
  · simpa only [mix, hi, ↓reduceIte, Function.comp_def] using (measurable_pi_apply i).comp measurable_snd

lemma mix_preserving {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (S : Finset ι) :
    MeasurePreserving (mix S)
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)))
      (Measure.pi (fun _ : ι => μ)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow α α ι
  have he := (measurePreserving_arrowProdEquivProdArrow α α ι (fun _ => μ) (fun _ => μ)).symm
  have hcoord (i : ι) : MeasurePreserving
      (fun p : α × α => if i ∈ S then p.1 else p.2) (μ.prod μ) μ := by
    by_cases hi : i ∈ S
    · simpa only [hi, ↓reduceIte] using (measurePreserving_fst (μ:=μ) (ν:=μ))
    · simpa only [hi, ↓reduceIte] using (measurePreserving_snd (μ:=μ) (ν:=μ))
  have hp := measurePreserving_pi (fun _ : ι => μ.prod μ) (fun _ : ι => μ) hcoord
  exact hp.comp he

lemma update_measurable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (i : ι) : Measurable (fun p : (ι → α) × α => Function.update p.1 i p.2) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j = i
  · subst j; simpa using (measurable_snd : Measurable (fun p : (ι→α)×α => p.2))
  · simpa only [Function.update_of_ne h, Function.comp_def] using (measurable_pi_apply j).comp measurable_fst

lemma update_preserving {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) :
    MeasurePreserving (fun p : (ι → α) × α => Function.update p.1 i p.2)
      ((Measure.pi (fun _ : ι => μ)).prod μ) (Measure.pi (fun _ : ι => μ)) := by
  let ν := Measure.pi (fun _ : ι => μ)
  have ha : MeasurePreserving (fun p : (ι→α)×(ι→α) => (p.1, p.2 i)) (ν.prod ν) (ν.prod μ) :=
    (MeasurePreserving.id ν).prod (measurePreserving_eval (fun _ : ι => μ) i)
  have hb : MeasurePreserving (fun p : (ι→α)×(ι→α) => Function.update p.1 i (p.2 i)) (ν.prod ν) ν := by
    have h := mix_preserving μ ({i}ᶜ : Finset ι)
    convert h using 1
    funext p j
    by_cases hj : j = i
    · subst j; simp [mix]
    · simp [mix, hj]
  refine ⟨update_measurable i, ?_⟩
  rw [← ha.map_eq, Measure.map_map (update_measurable i) ha.measurable]
  exact hb.map_eq

lemma integral_preserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {T : α → β} (hT : MeasurePreserving T μ ν)
    {g : β → ℝ} (hg : AEStronglyMeasurable g ν) :
    (∫ x, g (T x) ∂μ) = ∫ y, g y ∂ν := by
  rw [← hT.map_eq] at hg ⊢
  exact (integral_map hT.measurable.aemeasurable hg).symm

lemma integral_update {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) {g : (ι → α) → ℝ}
    (hg : Integrable g (Measure.pi (fun _ : ι => μ))) :
    (∫ x, ∫ t, g (Function.update x i t) ∂μ ∂Measure.pi (fun _ : ι => μ)) =
      ∫ x, g x ∂Measure.pi (fun _ : ι => μ) := by
  have hi := (update_preserving μ i).integrable_comp_of_integrable hg
  calc
    _ = ∫ p, g (Function.update p.1 i p.2) ∂(Measure.pi (fun _ : ι => μ)).prod μ :=
      (integral_prod _ hi).symm
    _ = _ := integral_preserving (update_preserving μ i) hg.aestronglyMeasurable

end LargeIndependentSets.ProductAveraging

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

noncomputable def unitCubeLaw (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => unitLaw)
instance unitCubeLaw_probability (n : ℕ) : IsProbabilityMeasure (unitCubeLaw n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => unitLaw)))

lemma unitCubeLaw_absolutelyContinuous (n : ℕ) :
    unitCubeLaw n ≪ (volume : Measure (Fin n → ℝ)) := by
  change Measure.pi (fun _ : Fin n => volume.restrict (Icc (0:ℝ) 1)) ≪ _
  rw [← Measure.restrict_pi_pi]
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self

lemma update_lipschitz {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    LipschitzWith 1 (Function.update x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro j
  by_cases h : j = i
  · subst j; simp
  · simp only [Function.update_of_ne h, dist_self]
    exact dist_nonneg

lemma slice_lipschitz {n : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (x : Fin n → ℝ) (i : Fin n) :
    LipschitzWith L (f ∘ Function.update x i) := by
  simpa only [mul_one] using hf.comp (update_lipschitz x i)

lemma variation_eq_integral_coordinate {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    variation (f ∘ Function.update x i) =
      ∫ t, |CubeGradient.coordinateDerivative f i (Function.update x i t)| ∂unitLaw := by
  rw [integral_unitLaw]
  unfold variation
  congr 1
  funext t
  simp only [CubeGradient.coordinateDerivative, Function.update_self, Function.comp_def,
    Function.update_idem]

lemma total_integral_slice_variation {n : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) :
    (∀ i, Integrable (fun x => variation (f ∘ Function.update x i)) (unitCubeLaw n)) ∧
    (∑ i, ∫ x, variation (f ∘ Function.update x i) ∂unitCubeLaw n) ≤ L := by
  obtain ⟨hi, hsum⟩ := CubeGradient.integral_total_coordinate_variation hf (unitCubeLaw n)
    (unitCubeLaw_absolutelyContinuous n)
  have he (i : Fin n) : (∫ x, variation (f ∘ Function.update x i) ∂unitCubeLaw n) =
      ∫ x, |CubeGradient.coordinateDerivative f i x| ∂unitCubeLaw n := by
    simp only [variation_eq_integral_coordinate]
    exact ProductAveraging.integral_update unitLaw i (hi i)
  refine ⟨?_, by simpa only [he] using hsum⟩
  intro i
  have hip := (ProductAveraging.update_preserving unitLaw i).integrable_comp_of_integrable (hi i)
  have heq : (fun x => variation (f ∘ Function.update x i)) =
      (fun x => ∫ t, |CubeGradient.coordinateDerivative f i (Function.update x i t)| ∂unitLaw) :=
    funext (fun x => variation_eq_integral_coordinate f x i)
  rw [heq]
  exact hip.integral_prod_left

noncomputable def seedLaw (m : ℕ) : Measure (Cube m × ℝ) := (uniformLaw (Cube m)).prod unitLaw
instance seedLaw_probability (m : ℕ) : IsProbabilityMeasure (seedLaw m) := by unfold seedLaw; infer_instance
noncomputable def seedCubeLaw (n m : ℕ) : Measure (Fin n → Cube m × ℝ) :=
  Measure.pi (fun _ => seedLaw m)
instance seedCubeLaw_probability (n m : ℕ) : IsProbabilityMeasure (seedCubeLaw n m) := by
  unfold seedCubeLaw; infer_instance

noncomputable def cubeSampler {n m : ℕ} (p : Fin n → Cube m × ℝ) : Fin n → ℝ :=
  fun i => scalarSampler m (p i)

lemma cubeSampler_preserving (n m : ℕ) :
    MeasurePreserving (cubeSampler (n:=n) (m:=m)) (seedCubeLaw n m) (unitCubeLaw n) :=
  measurePreserving_pi (fun _ : Fin n => seedLaw m) (fun _ => unitLaw)
    (fun _ => scalarSampler_preserving m)

lemma cubeSampler_update {n m : ℕ} (p : Fin n → Cube m × ℝ) (i : Fin n) (t : Cube m × ℝ) :
    cubeSampler (Function.update p i t) = Function.update (cubeSampler p) i (scalarSampler m t) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [cubeSampler]
  · simp [cubeSampler, hj]

noncomputable def flipSeed {m : ℕ} (k : Fin m) (t : Cube m × ℝ) : Cube m × ℝ :=
  (flip k t.1, t.2)

lemma flipSeed_measurable {m : ℕ} (k : Fin m) : Measurable (flipSeed k) :=
  ((measurable_of_countable (flip k)).comp measurable_fst).prodMk measurable_snd

noncomputable def sampledDiff {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (k : Fin m) (p : Fin n → Cube m × ℝ) : ℝ :=
  |(f (cubeSampler p) - f (cubeSampler (Function.update p i (flipSeed k (p i)))))/2|

lemma sampledDiff_measurable {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (i : Fin n) (k : Fin m) : Measurable (sampledDiff f i k) := by
  have hu : Measurable (fun p : Fin n → Cube m × ℝ => Function.update p i (flipSeed k (p i))) :=
    (ProductAveraging.update_measurable i).comp
      (measurable_id.prodMk ((flipSeed_measurable k).comp (measurable_pi_apply i)))
  exact (((hf.comp (cubeSampler_preserving n m).measurable).sub
    (hf.comp ((cubeSampler_preserving n m).measurable.comp hu))).div_const 2).abs

lemma sampledDiff_le_one {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hb : ∀ x, |f x| ≤ 1) (i : Fin n) (k : Fin m) (p : Fin n → Cube m × ℝ) :
    sampledDiff f i k p ≤ 1 := by
  unfold sampledDiff
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := (abs_sub (f (cubeSampler p))
    (f (cubeSampler (Function.update p i (flipSeed k (p i)))))).trans
      (add_le_add (hb _) (hb _))
  linarith

lemma sampledDiff_integrable {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) (i : Fin n) (k : Fin m) :
    Integrable (sampledDiff f i k) (seedCubeLaw n m) := by
  apply Integrable.of_bound (sampledDiff_measurable hf i k).aestronglyMeasurable 1
  filter_upwards [] with p
  simp only [Real.norm_eq_abs, sampledDiff, abs_abs]
  exact sampledDiff_le_one hb i k p

lemma sampledDiff_fiber {n m : ℕ} (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (k : Fin m) (p : Fin n → Cube m × ℝ) (t : Cube m × ℝ) :
    sampledDiff f i k (Function.update p i t) =
      |((f ∘ Function.update (cubeSampler p) i) (scalarCell t.1 t.2) -
        (f ∘ Function.update (cubeSampler p) i) (scalarCell (flip k t.1) t.2))/2| := by
  simp only [sampledDiff, Function.update_self, Function.update_idem,
    cubeSampler_update, flipSeed, scalarSampler, Function.comp_def]

lemma integral_sampledDiff_fiber {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1)
    (i : Fin n) (k : Fin m) (p : Fin n → Cube m × ℝ) :
    (∫ t, sampledDiff f i k (Function.update p i t) ∂seedLaw m) =
      scalarSampleInfluence (f ∘ Function.update (cubeSampler p) i) k := by
  have hu : Measurable (Function.update p i) := by
    simpa only [Function.comp_def, id_eq] using
      (ProductAveraging.update_measurable i).comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun t => sampledDiff f i k (Function.update p i t)) (seedLaw m) := by
    apply Integrable.of_bound ((sampledDiff_measurable hf i k).comp hu).aestronglyMeasurable 1
    filter_upwards [] with t
    simp only [Real.norm_eq_abs, Function.comp_def, sampledDiff, abs_abs]
    exact sampledDiff_le_one hb i k _
  rw [seedLaw, integral_prod _ hi, integral_uniformLaw]
  simp only [sampledDiff_fiber, integral_unitLaw, scalarSampleInfluence, mean]

theorem total_sampled_influence {n m : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (hb : ∀ x, |f x| ≤ 1) :
    (∑ i : Fin n, ∑ k : Fin m, ∫ p, sampledDiff f i k p ∂seedCubeLaw n m) ≤ L := by
  obtain ⟨hv, ht⟩ := total_integral_slice_variation hf
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) ht
  have hi (k : Fin m) := sampledDiff_integrable hf.continuous.measurable hb i k
  have hfi (k : Fin m) : Integrable (fun p =>
      scalarSampleInfluence (f ∘ Function.update (cubeSampler p) i) k) (seedCubeLaw n m) := by
    have h := ((ProductAveraging.update_preserving (seedLaw m) i).integrable_comp_of_integrable (hi k)).integral_prod_left
    simpa only [Function.comp_def, integral_sampledDiff_fiber hf.continuous.measurable hb,
      seedCubeLaw] using h
  have he (k : Fin m) : (∫ p, sampledDiff f i k p ∂seedCubeLaw n m) =
      ∫ p, scalarSampleInfluence (f ∘ Function.update (cubeSampler p) i) k ∂seedCubeLaw n m := by
    change (∫ p, sampledDiff f i k p ∂Measure.pi (fun _ => seedLaw m)) = _
    rw [← ProductAveraging.integral_update (seedLaw m) i (hi k)]
    simp only [integral_sampledDiff_fiber hf.continuous.measurable hb, seedCubeLaw]
  simp only [he]
  rw [← integral_finsetSum _ (fun k _ => hfi k)]
  have hvp := (cubeSampler_preserving n m).integrable_comp_of_integrable (hv i)
  calc
    _ ≤ ∫ p, variation (f ∘ Function.update (cubeSampler p) i) ∂seedCubeLaw n m := by
      apply integral_mono (integrable_finsetSum _ (fun k _ => hfi k)) hvp
      intro p
      exact dyadic_sample_total_influence (slice_lipschitz hf _ _)
    _ = ∫ x, variation (f ∘ Function.update x i) ∂unitCubeLaw n :=
      ProductAveraging.integral_preserving (cubeSampler_preserving n m) (hv i).aestronglyMeasurable

end LargeIndependentSets.BooleanJunta

end OAI

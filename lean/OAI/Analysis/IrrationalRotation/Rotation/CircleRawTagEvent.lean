import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitDensity
import OAI.Analysis.IrrationalRotation.Analysis.TruncationEvent

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

section Parameters
variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
include hκ0 hκ hm ha ha' hb hb' ht0 ht

lemma rawLaw_map_endpoint_density (side : Bool) :
    (rawLaw κ m a b t).map (endpoint side) = baseLaw.withDensity
      (fun x => ENNReal.ofReal (marginalDensity side κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 2 ≤ 2 * m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure hm2 ha0 ha' hb0 hb'
  have hq : 0 ≤ diagonalMass κ m a b t :=
    le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have hp := componentProbabilities_nonneg (a := a) (b := b) hκ0 hm0 ht0
  cases side
  · change ((labelledMixture baseLaw (ENNReal.ofReal (diagonalMass κ m a b t))
      (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
      (leftLaw (2 * m) a b) (rightLaw (2 * m) a b)).map
      (Prod.fst ∘ Prod.snd)) = _
    rw [← Measure.map_map measurable_fst measurable_snd, labelledMixture_map_snd]
    exact mixture_fst_real_density baseLaw _ _ _ _
      (fun i => leftDensity (2 * m) a b i) hq hp
      (fun i x => (leftDensity_bound hm2 ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (leftLaw_eq_withDensity hm2 ha0 ha' hb0 hb')
  · change ((labelledMixture baseLaw (ENNReal.ofReal (diagonalMass κ m a b t))
      (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
      (leftLaw (2 * m) a b) (rightLaw (2 * m) a b)).map
      (Prod.snd ∘ Prod.snd)) = _
    rw [← Measure.map_map measurable_snd measurable_snd, labelledMixture_map_snd]
    exact mixture_snd_real_density baseLaw _ _ _ _
      (fun i => rightDensity (2 * m) a b i) hq hp
      (fun i x => (rightDensity_bound hm2 ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (rightLaw_eq_withDensity hm2 ha0 ha' hb0 hb')

lemma rawLaw_map_endpoint_le_ten (side : Bool) :
    (rawLaw κ m a b t).map (endpoint side) ≤ (10 : ℝ≥0∞) • baseLaw := by
  rw [rawLaw_map_endpoint_density hκ0 hκ hm ha ha' hb hb' ht0 ht]
  calc
    _ ≤ baseLaw.withDensity (fun _ => (10 : ℝ≥0∞)) := by
      apply withDensity_mono
      exact Filter.Eventually.of_forall (fun x => by
        exact le_trans (ENNReal.ofReal_le_ofReal
          (marginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht side x).2.2.le)
          (by norm_num))
    _ = _ := withDensity_const _

end Parameters

lemma rawLaw_tag_mass {κ m a b t : ℝ} (hm : 1 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    rawLaw κ m a b t {z | z.1 = some (4 : Fin 5)} = ENNReal.ofReal (t / m) := by
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha1 hb0 hb1
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha1 hb0 hb1
  exact labelledMixture_some_mass _ _ _ _ _ (4 : Fin 5)

theorem rawLaw_ae_tag_interval (κ m a b t : ℝ) :
    ∀ᵐ z ∂rawLaw κ m a b t, z.1 = some (4 : Fin 5) →
      z.2.1 < 1 / (2 * m) ∧ 1 - 1 / (2 * m) ≤ z.2.2 := by
  let P : Option (Fin 5) × (ℝ × ℝ) → Prop := fun z =>
    z.1 = some (4 : Fin 5) → z.2.1 < 1 / (2 * m) ∧ 1 - 1 / (2 * m) ≤ z.2.2
  have hP : MeasurableSet {z | P z} := by
    simp only [P, imp_iff_not_or]
    change MeasurableSet ({z : Option (Fin 5) × (ℝ × ℝ) | z.1 = some (4 : Fin 5)}ᶜ ∪
      {z : Option (Fin 5) × (ℝ × ℝ) | z.2.1 < 1 / (2 * m) ∧ 1 - 1 / (2 * m) ≤ z.2.2})
    exact (measurable_fst (measurableSet_singleton _)).compl.union
      ((measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
       (measurableSet_le measurable_const (measurable_snd.comp measurable_snd)))
  change ∀ᵐ z ∂rawLaw κ m a b t, P z
  rw [rawLaw, labelledMixture, ae_add_measure_iff, ae_finsetSum_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hP).2
    exact Filter.Eventually.of_forall (by intro z; simp [P])
  · intro i _
    apply Measure.ae_smul_measure
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hP).2
    by_cases hi : i = 4
    · subst i
      change ∀ᵐ z ∂(intervalLaw 0 (1 / (2 * m))).prod (intervalLaw (1 - 1 / (2 * m)) 1),
        P (some 4, z)
      have : IsZeroOrProbabilityMeasure (intervalLaw 0 (1 / (2 * m))) := inferInstanceAs
        (IsZeroOrProbabilityMeasure (volume[|Ico 0 (1 / (2 * m))]))
      have : IsZeroOrProbabilityMeasure (intervalLaw (1 - 1 / (2 * m)) 1) := inferInstanceAs
        (IsZeroOrProbabilityMeasure (volume[|Ico (1 - 1 / (2 * m)) 1]))
      have hs : MeasurableSet {z : ℝ × ℝ | P (some 4, z)} :=
        hP.preimage (measurable_const.prodMk measurable_id)
      rw [Measure.ae_prod_iff_ae_ae hs]
      filter_upwards [intervalLaw_ae_mem 0 (1 / (2 * m))] with x hx
      filter_upwards [intervalLaw_ae_mem (1 - 1 / (2 * m)) 1] with y hy
      exact fun _ => ⟨hx.2, hy.1⟩
    · exact Filter.Eventually.of_forall (by intro z; simp [P, hi])

theorem concrete_circle_currentBlock_mass (m : ℕ) (hm : 200 ≤ m)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100)
    (a b : Fin m → ℝ)
    (ha : ∀ i, 1 / (m : ℝ) ≤ a i) (ha' : ∀ i, a i ≤ 1 / 4)
    (hb : ∀ i, 1 / (m : ℝ) ≤ b i) (hb' : ∀ i, b i ≤ 1 / 4) :
    Real.exp (-90) ≤
      (Measure.pi (fun i => rawLaw κ m (a i) (b i) 1)).real
        {z | (∃ i, (z i).1 = some (4 : Fin 5)) ∧
          ∀ i, (z i).2.1 < 1 - 3 / (m : ℝ) ∧ 3 / (m : ℝ) < (z i).2.2} := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hm100 : (100 : ℝ) ≤ m := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  let μ := fun i : Fin m => rawLaw κ m (a i) (b i) 1
  have : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    rawLaw_isProbabilityMeasure hκ0 hκ hm100 (ha i) (ha' i) (hb i) (hb' i)
      (by norm_num) (by norm_num)
  let T : Fin m → Set CoordinateSample := fun _ => {z | z.1 = some (4 : Fin 5)}
  have hT : ∀ i, MeasurableSet (T i) := fun _ =>
    measurable_fst (measurableSet_singleton _)
  have hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ) := by
    intro i
    change (rawLaw κ m (a i) (b i) 1).real {z | z.1 = some (4 : Fin 5)} = _
    rw [measureReal_def, rawLaw_tag_mass hm1 (width_pos hm0 (ha i)) (ha' i)
      (width_pos hm0 (hb i)) (hb' i), ENNReal.toReal_ofReal (by positivity)]
  have hinv : 1 / (m : ℝ) ≤ 1 / 200 :=
    (div_le_div_iff₀ hm0 (by norm_num)).2 (by linarith)
  have hinvhalf : 1 / (2 * (m : ℝ)) = (1 / (m : ℝ)) / 2 := by ring
  have hSafe : ∀ i, ∀ᵐ z ∂μ i, z ∈ T i →
      z.2.1 < 1 - 3 / (m : ℝ) ∧ 3 / (m : ℝ) < z.2.2 := by
    intro i
    filter_upwards [rawLaw_ae_tag_interval κ m (a i) (b i) 1] with z hz
    intro ht
    obtain ⟨hx, hy⟩ := hz ht
    rw [hinvhalf] at hx hy
    rw [show (3 : ℝ) / m = 3 * (1 / (m : ℝ)) by ring]
    constructor <;> linarith
  have hdomX : ∀ i, (μ i).map (fun z => z.2.1) ≤
      ENNReal.ofReal 10 • volume.restrict (Ico (0 : ℝ) 1) := by
    intro i
    have h := rawLaw_map_endpoint_le_ten hκ0 hκ hm100 (ha i) (ha' i) (hb i) (hb' i)
      (t := 1) (by norm_num) (by norm_num) false
    change (μ i).map (fun z => z.2.1) ≤ (10 : ℝ≥0∞) • baseLaw at h
    simpa only [baseLaw_eq_restrict, show ENNReal.ofReal 10 = (10 : ℝ≥0∞) by norm_num] using h
  have hdomY : ∀ i, (μ i).map (fun z => z.2.2) ≤
      ENNReal.ofReal 10 • volume.restrict (Ico (0 : ℝ) 1) := by
    intro i
    have h := rawLaw_map_endpoint_le_ten hκ0 hκ hm100 (ha i) (ha' i) (hb i) (hb' i)
      (t := 1) (by norm_num) (by norm_num) true
    change (μ i).map (fun z => z.2.2) ≤ (10 : ℝ≥0∞) • baseLaw at h
    simpa only [baseLaw_eq_restrict, show ENNReal.ofReal 10 = (10 : ℝ≥0∞) by norm_num] using h
  have hbudget : 0 ≤ 1 - (1 + 2 * ((10 : ℝ) * 3)) / (m : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hm0).mpr (by linarith)
  have h := InvariantRotation.TruncationEvent.currentBlock_mass_lower_bound_ae m
    (by omega) μ T hT (fun _ => measurable_fst.comp measurable_snd)
    (fun _ => measurable_snd.comp measurable_snd) (C := 10) (a := 3)
    (by norm_num) (by norm_num) hbudget hTag hSafe hdomX hdomY
  norm_num only [show (1 : ℝ) + 2 * (10 * 3) = 61 by norm_num] at h
  exact (InvariantRotation.TaggedEventBounds.circle_tag_bound m hm).trans h

end Invariant233.CircleDigitCoupling

end

end OAI

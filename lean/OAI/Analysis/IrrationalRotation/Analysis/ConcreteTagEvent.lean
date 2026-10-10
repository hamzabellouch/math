import OAI.Analysis.IrrationalRotation.Product.OneCoordinateDensity
import OAI.Analysis.IrrationalRotation.Analysis.TruncationEvent

namespace OAI

open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

namespace Invariant233.OneCoordinateCoupling

open CouplingMixture CouplingMarginalBounds

theorem labelledLaw_ae_tag_interval (κ m a b t : ℝ) :
    ∀ᵐ z ∂labelledLaw κ m a b t, z.1 = some (4 : Fin 5) →
      z.2.1 < 1 / m ∧ 1 - 1 / m ≤ z.2.2 := by
  let P : Option (Fin 5) × (ℝ × ℝ) → Prop := fun z =>
    z.1 = some (4 : Fin 5) → z.2.1 < 1 / m ∧ 1 - 1 / m ≤ z.2.2
  have hP : MeasurableSet {z | P z} := by
    simp only [P, imp_iff_not_or]
    change MeasurableSet ({z : Option (Fin 5) × (ℝ × ℝ) | z.1 = some (4 : Fin 5)}ᶜ ∪
      {z : Option (Fin 5) × (ℝ × ℝ) | z.2.1 < 1 / m ∧ 1 - 1 / m ≤ z.2.2})
    exact (measurable_fst (measurableSet_singleton _)).compl.union
      ((measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
       (measurableSet_le measurable_const (measurable_snd.comp measurable_snd)))
  change ∀ᵐ z ∂labelledLaw κ m a b t, P z
  rw [labelledLaw, labelledMixture, ae_add_measure_iff, ae_finsetSum_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hP).2
    exact Filter.Eventually.of_forall (by intro z; simp [P])
  · intro i _
    apply Measure.ae_smul_measure
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hP).2
    by_cases hi : i = 4
    · subst i
      change ∀ᵐ z ∂(intervalLaw 0 (1 / m)).prod (intervalLaw (1 - 1 / m) 1),
        P (some 4, z)
      have : IsZeroOrProbabilityMeasure (intervalLaw 0 (1 / m)) := inferInstanceAs
        (IsZeroOrProbabilityMeasure (volume[|Ico 0 (1 / m)]))
      have : IsZeroOrProbabilityMeasure (intervalLaw (1 - 1 / m) 1) := inferInstanceAs
        (IsZeroOrProbabilityMeasure (volume[|Ico (1 - 1 / m) 1]))
      have hs : MeasurableSet {z : ℝ × ℝ | P (some 4, z)} :=
        hP.preimage (measurable_const.prodMk measurable_id)
      rw [Measure.ae_prod_iff_ae_ae hs]
      filter_upwards [intervalLaw_ae_mem 0 (1 / m)] with x hx
      filter_upwards [intervalLaw_ae_mem (1 - 1 / m) 1] with y hy
      exact fun _ => ⟨hx.2, hy.1⟩
    · exact Filter.Eventually.of_forall (by intro z; simp [P, hi])

theorem labelledLaw_left_map (κ m a b t : ℝ) :
    (labelledLaw κ m a b t).map (fun z => z.2.1) = (pairLaw κ m a b t).fst := by
  change _ = (pairLaw κ m a b t).map Prod.fst
  rw [← labelledLaw_map_snd, Measure.map_map measurable_fst measurable_snd]
  rfl

theorem labelledLaw_right_map (κ m a b t : ℝ) :
    (labelledLaw κ m a b t).map (fun z => z.2.2) = (pairLaw κ m a b t).snd := by
  change _ = (pairLaw κ m a b t).map Prod.snd
  rw [← labelledLaw_map_snd, Measure.map_map measurable_snd measurable_snd]
  rfl

theorem concrete_product_currentBlock_mass (m : ℕ) (hm : 100 ≤ m)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100)
    (a b : Fin m → ℝ)
    (ha : ∀ i, 1 / (m : ℝ) ≤ a i) (ha' : ∀ i, a i ≤ 1 / 4)
    (hb : ∀ i, 1 / (m : ℝ) ≤ b i) (hb' : ∀ i, b i ≤ 1 / 4) :
    Real.exp (-82) ≤
      (Measure.pi (fun i => labelledLaw κ m (a i) (b i) 1)).real
        {z | (∃ i, (z i).1 = some (4 : Fin 5)) ∧
          ∀ i, (z i).2.1 < 1 - 2 / (m : ℝ) ∧ 2 / (m : ℝ) < (z i).2.2} := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm2 : (2 : ℝ) ≤ m := by linarith
  let μ := fun i : Fin m => labelledLaw κ m (a i) (b i) 1
  have : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    labelledLaw_isProbabilityMeasure hκ0 hκ hmR (ha i) (ha' i) (hb i) (hb' i)
      (by norm_num) (by norm_num)
  let T : Fin m → Set (Option (Fin 5) × (ℝ × ℝ)) :=
    fun _ => {z | z.1 = some (4 : Fin 5)}
  have hT : ∀ i, MeasurableSet (T i) := fun _ =>
    measurable_fst (measurableSet_singleton _)
  have hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ) := by
    intro i
    change (labelledLaw κ m (a i) (b i) 1).real {z | z.1 = some (4 : Fin 5)} = _
    rw [measureReal_def, labelledLaw_tag_mass hm2 (width_pos hm0 (ha i)) (ha' i)
      (width_pos hm0 (hb i)) (hb' i), ENNReal.toReal_ofReal (by positivity)]
  have hinv : 1 / (m : ℝ) ≤ 1 / 100 :=
    (div_le_div_iff₀ hm0 (by norm_num)).2 (by linarith)
  have hSafe : ∀ i, ∀ᵐ z ∂μ i, z ∈ T i →
      z.2.1 < 1 - 2 / (m : ℝ) ∧ 2 / (m : ℝ) < z.2.2 := by
    intro i
    filter_upwards [labelledLaw_ae_tag_interval κ m (a i) (b i) 1] with z hz
    intro ht
    obtain ⟨hx, hy⟩ := hz ht
    rw [show (2 : ℝ) / m = 2 * (1 / (m : ℝ)) by ring]
    constructor <;> linarith
  have hdomX : ∀ i, (μ i).map (fun z => z.2.1) ≤
      ENNReal.ofReal 10 • volume.restrict (Ico (0 : ℝ) 1) := by
    intro i
    change (labelledLaw κ m (a i) (b i) 1).map _ ≤ _
    rw [labelledLaw_left_map, ← baseLaw_eq_restrict]
    simpa using pairLaw_fst_le_ten hκ0 hκ hmR (ha i) (ha' i) (hb i) (hb' i)
      (t := 1) (by norm_num) (by norm_num)
  have hdomY : ∀ i, (μ i).map (fun z => z.2.2) ≤
      ENNReal.ofReal 10 • volume.restrict (Ico (0 : ℝ) 1) := by
    intro i
    change (labelledLaw κ m (a i) (b i) 1).map _ ≤ _
    rw [labelledLaw_right_map, ← baseLaw_eq_restrict]
    simpa using pairLaw_snd_le_ten hκ0 hκ hmR (ha i) (ha' i) (hb i) (hb' i)
      (t := 1) (by norm_num) (by norm_num)
  have hbudget : 0 ≤ 1 - (1 + 2 * ((10 : ℝ) * 2)) / (m : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hm0).mpr (by linarith)
  have h := InvariantRotation.TruncationEvent.currentBlock_mass_lower_bound_ae m
    (by omega) μ T hT (fun _ => measurable_fst.comp measurable_snd)
    (fun _ => measurable_snd.comp measurable_snd) (C := 10) (a := 2)
    (by norm_num) (by norm_num) hbudget hTag hSafe hdomX hdomY
  norm_num only [show (1 : ℝ) + 2 * (10 * 2) = 41 by norm_num] at h
  exact (InvariantRotation.TaggedEventBounds.product_tag_bound m hm).trans h

end Invariant233.OneCoordinateCoupling

end OAI

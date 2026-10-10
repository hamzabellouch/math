import OAI.Analysis.IrrationalRotation.Model.ProductTailTrimming
import OAI.Analysis.IrrationalRotation.Model.ProductSampling
import OAI.Analysis.IrrationalRotation.Product.ProductCocycle
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel.TailTrimming

theorem fract_add_eq_fract_add_fract (u t : ℝ) :
    Int.fract (u + t) = Int.fract (u + Int.fract t) := by
  conv_lhs => rw [← Int.floor_add_fract t]
  rw [show u + ((⌊t⌋ : ℝ) + Int.fract t) =
    (u + Int.fract t) + (⌊t⌋ : ℝ) by ring]
  exact Int.fract_add_intCast _ _

theorem fract_add_lt_iff {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) (t : ℝ) :
    Int.fract (u + t) < u ↔ 1 - Int.fract t ≤ u := by
  rw [fract_add_eq_fract_add_fract]
  have hr0 := Int.fract_nonneg t
  have hr1 := Int.fract_lt_one t
  by_cases h : u + Int.fract t < 1
  · have hf : ⌊u + Int.fract t⌋ = (0 : ℤ) :=
      Int.floor_eq_zero_iff.mpr ⟨add_nonneg hu.1 hr0, h⟩
    rw [Int.fract, hf, Int.cast_zero, sub_zero]
    constructor <;> intro hh <;> linarith
  · have hf : ⌊u + Int.fract t⌋ = (1 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num <;> linarith [hu.2]
    rw [Int.fract, hf, Int.cast_one]
    constructor <;> intro hh <;> linarith

theorem uniform_wrap_measure (t : ℝ) :
    (volume.restrict (Ico (0 : ℝ) 1)) {u : ℝ | Int.fract (u + t) < u} =
      ENNReal.ofReal (Int.fract t) := by
  have hm : MeasurableSet {u : ℝ | Int.fract (u + t) < u} :=
    measurableSet_lt ((measurable_id.add_const t).fract) measurable_id
  rw [Measure.restrict_apply hm]
  have heq : {u : ℝ | Int.fract (u + t) < u} ∩ Ico 0 1 =
      Ico (1 - Int.fract t) 1 := by
    ext u
    constructor
    · rintro ⟨h, hu⟩
      exact ⟨(fract_add_lt_iff hu t).mp h, hu.2⟩
    · rintro ⟨hl, hr⟩
      have hu : u ∈ Ico (0 : ℝ) 1 :=
        ⟨by linarith [Int.fract_lt_one t], hr⟩
      exact ⟨(fract_add_lt_iff hu t).mpr hl, hu⟩
  rw [heq, Real.volume_Ico]
  congr 1
  ring

theorem measurableSet_coordinateOrderFailure (θ : ℕ → ℝ) (n i : ℕ) :
    MeasurableSet (coordinateOrderFailure θ n i) := by
  have hr : Measurable circleRepresentative :=
    ProductCocycle.measurable_representative
  exact measurableSet_lt
    (hr.comp ((measurable_pi_apply i).add_const _))
    (hr.comp (measurable_pi_apply i))

theorem coordinateOrderFailure_measure (θ : ℕ → ℝ) (n i : ℕ) :
    baseMeasure (coordinateOrderFailure θ n i) =
      ENNReal.ofReal (Int.fract ((n : ℝ) * θ i)) := by
  have hmp := CocycleSupport.measurePreserving_productRepresentative (ι := ℕ) i
  have hm : MeasurableSet {u : ℝ | Int.fract (u + (n : ℝ) * θ i) < u} :=
    measurableSet_lt ((measurable_id.add_const _).fract) measurable_id
  have heq : coordinateOrderFailure θ n i =
      (fun x : Base => circleRepresentative (x i)) ⁻¹'
        {u : ℝ | Int.fract (u + (n : ℝ) * θ i) < u} := by
    ext x
    simp only [coordinateOrderFailure, rotationIterate, Set.mem_ofPred_eq,
      Int.cast_natCast, Set.mem_preimage]
    exact Iff.of_eq (congrArg (fun r : ℝ => r < circleRepresentative (x i))
      (ProductCocycle.representative_add (x i) ((n : ℝ) * θ i)))
  rw [heq]
  change (Measure.infinitePi (fun _ : ℕ => (volume : Measure UnitAddCircle))) _ = _
  exact (hmp.measure_preimage hm.nullMeasurableSet).trans (uniform_wrap_measure _)

theorem measurableSet_tailOrderFailure (I : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (tailOrderFailure I θ n) :=
  MeasurableSet.iUnion (fun i => measurableSet_coordinateOrderFailure θ n i)

theorem tailOrderFailure_measure_le (I : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ) :
    baseMeasure (tailOrderFailure I θ n) ≤
      ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal (Int.fract ((n : ℝ) * θ i)) := by
  exact (measure_iUnion_le _).trans_eq
    (tsum_congr (fun i => coordinateOrderFailure_measure θ n i))

theorem tailOrderFailure_measure_le_angles (I : Finset ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (n : ℕ) :
    baseMeasure (tailOrderFailure I θ n) ≤
      ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal ((n : ℝ) * θ i) := by
  refine (tailOrderFailure_measure_le I θ n).trans (ENNReal.tsum_le_tsum ?_)
  intro i
  apply ENNReal.ofReal_le_ofReal
  have hf : (0 : ℤ) ≤ ⌊(n : ℝ) * θ i⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) (hθ i))
  have hf' : (0 : ℝ) ≤ (⌊(n : ℝ) * θ i⌋ : ℝ) := by exact_mod_cast hf
  rw [Int.fract]
  linarith

theorem indepFun_coordinate_restrictions (S T : Set ℕ) (hST : Disjoint S T) :
    IndepFun (fun x : Base => fun i : S => x i)
      (fun x : Base => fun i : T => x i) baseMeasure := by
  have hi : iIndepFun (fun i (x : Base) => x i) baseMeasure :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have h := indep_iSup_of_disjoint
    (fun i : ℕ => (measurable_pi_apply i : Measurable (fun x : Base => x i)).comap_le)
    hi hST
  change Indep (MeasurableSpace.comap (fun x : Base => fun i : S => x i) inferInstance)
    (MeasurableSpace.comap (fun x : Base => fun i : T => x i) inferInstance) baseMeasure
  simp_rw [MeasurableSpace.comap_process_pi]
  simpa only [iSup_subtype] using h

theorem withDensity_tail_event (I : Finset ℕ)
    (w : (I → Circle) → ℝ≥0∞) (hw : Measurable w)
    (B : Set ({i : ℕ // i ∉ I} → Circle)) (hB : MeasurableSet B) :
    (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i)))
        ((fun x : Base => fun i : {i : ℕ // i ∉ I} => x i) ⁻¹' B) =
      (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i))) univ *
        baseMeasure ((fun x : Base => fun i : {i : ℕ // i ∉ I} => x i) ⁻¹' B) := by
  let P : Base → (I → Circle) := fun x i => x i
  let Q : Base → ({i : ℕ // i ∉ I} → Circle) := fun x i => x i
  have hP : Measurable P := by fun_prop
  have hQ : Measurable Q := by fun_prop
  have hpre : MeasurableSet (Q ⁻¹' B) := hQ hB
  have hind : IndepFun P Q baseMeasure :=
    indepFun_coordinate_restrictions (I : Set ℕ) (I : Set ℕ)ᶜ disjoint_compl_right
  have hind' := hind.comp hw (measurable_const.indicator hB :
    Measurable (B.indicator (fun _ => (1 : ℝ≥0∞))))
  have hh := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hw.comp hP) ((measurable_const.indicator hB).comp hQ) hind'
  have heq : (fun x : Base => w (P x) * B.indicator (fun _ => (1 : ℝ≥0∞)) (Q x)) =
      (Q ⁻¹' B).indicator (fun x => w (P x)) := by
    funext x
    by_cases hx : Q x ∈ B <;> simp [hx]
  have heq1 : (fun x : Base => B.indicator (fun _ => (1 : ℝ≥0∞)) (Q x)) =
      (Q ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : Q x ∈ B <;> simp [hx]
  change (∫⁻ x, w (P x) * B.indicator (fun _ => (1 : ℝ≥0∞)) (Q x) ∂baseMeasure) =
    (∫⁻ x, w (P x) ∂baseMeasure) *
      (∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) (Q x) ∂baseMeasure) at hh
  rw [heq, heq1, lintegral_indicator hpre, lintegral_indicator_const hpre, one_mul] at hh
  change (baseMeasure.withDensity (fun x => w (P x))) (Q ⁻¹' B) =
    (baseMeasure.withDensity (fun x => w (P x))) univ * baseMeasure (Q ⁻¹' B)
  simpa only [withDensity_apply _ hpre,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hh

theorem weighted_tailOrderFailure_eq (I : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ)
    (w : (I → Circle) → ℝ≥0∞) (hw : Measurable w) :
    (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i)))
        (tailOrderFailure I θ n) =
      (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i))) univ *
        baseMeasure (tailOrderFailure I θ n) := by
  let B : Set ({i : ℕ // i ∉ I} → Circle) :=
    ⋃ i : {i : ℕ // i ∉ I},
      {y | circleRepresentative (y i + ((n : ℝ) * θ i : ℝ)) <
        circleRepresentative (y i)}
  have hr : Measurable circleRepresentative := ProductCocycle.measurable_representative
  have hB : MeasurableSet B := by
    apply MeasurableSet.iUnion
    intro i
    exact measurableSet_lt (hr.comp ((measurable_pi_apply i).add_const _))
      (hr.comp (measurable_pi_apply i))
  have heq : tailOrderFailure I θ n =
      (fun x : Base => fun i : {i : ℕ // i ∉ I} => x i) ⁻¹' B := by
    ext x
    simp only [tailOrderFailure, coordinateOrderFailure, B, rotationIterate,
      mem_iUnion, mem_ofPred_eq, mem_preimage, Int.cast_natCast]
  rw [heq]
  exact withDensity_tail_event I w hw B hB

theorem weighted_tailOrderFailure_le (I : Finset ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (n : ℕ)
    (w : (I → Circle) → ℝ≥0∞) (hw : Measurable w) :
    (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i)))
        (tailOrderFailure I θ n) ≤
      (baseMeasure.withDensity (fun x : Base => w (fun i : I => x i))) univ *
        (ENNReal.ofReal (n : ℝ) * ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal (θ i)) := by
  rw [weighted_tailOrderFailure_eq I θ n w hw]
  apply mul_le_mul_right
  convert tailOrderFailure_measure_le_angles I θ hθ n using 1
  simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.tsum_mul_left]

theorem not_mem_tailOrderFailure_iff (I : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
    x ∉ tailOrderFailure I θ n ↔
      ∀ i, i ∉ I → circleRepresentative (x i) ≤
        circleRepresentative (rotationIterate θ (n : ℤ) x i) := by
  simp only [tailOrderFailure, coordinateOrderFailure, mem_iUnion,
    mem_ofPred_eq, not_exists, not_lt, Subtype.forall]

theorem measurable_orbitPairMap (θ : ℕ → ℝ) (n : ℕ) :
    Measurable (orbitPairMap θ n) := by
  apply measurable_id.prodMk
  apply Measurable.of_eval
  intro i
  exact (measurable_pi_apply i).add_const _

theorem measurableSet_orderedPairEvent : MeasurableSet orderedPairEvent := by
  have hr : Measurable circleRepresentative := ProductCocycle.measurable_representative
  simp only [orderedPairEvent, Ordered, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (hr.comp ((measurable_pi_apply i).comp measurable_fst))
    (hr.comp ((measurable_pi_apply i).comp measurable_snd))

theorem orbitPairMeasure_mass (θ : ℕ → ℝ) (n : ℕ) (w : Base → ℝ≥0∞) :
    orbitPairMeasure θ n w univ = (baseMeasure.withDensity w) univ := by
  rw [orbitPairMeasure, Measure.map_apply (measurable_orbitPairMap θ n) MeasurableSet.univ]
  simp

theorem orbitPairMeasure_unordered_le (I : Finset ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (n : ℕ)
    (w : (I → Circle) → ℝ≥0∞) (hw : Measurable w)
    (hprefix : ∀ᵐ x ∂baseMeasure.withDensity (fun x : Base => w (fun i : I => x i)),
      ∀ i ∈ I, circleRepresentative (x i) ≤
        circleRepresentative (rotationIterate θ (n : ℤ) x i)) :
    orbitPairMeasure θ n (fun x : Base => w (fun i : I => x i)) orderedPairEventᶜ ≤
      orbitPairMeasure θ n (fun x : Base => w (fun i : I => x i)) univ *
        (ENNReal.ofReal (n : ℝ) * ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal (θ i)) := by
  rw [orbitPairMeasure_mass]
  refine le_trans ?_ (weighted_tailOrderFailure_le I θ hθ n w hw)
  rw [orbitPairMeasure, Measure.map_apply (measurable_orbitPairMap θ n)
    measurableSet_orderedPairEvent.compl]
  apply measure_mono_ae
  filter_upwards [hprefix] with x hx
  intro hbad
  by_contra htail
  have ht := (not_mem_tailOrderFailure_iff I θ n x).mp htail
  apply hbad
  change Ordered x (rotationIterate θ (n : ℤ) x)
  intro i
  by_cases hi : i ∈ I
  · exact hx i hi
  · exact ht i hi

theorem orbitAverageMeasure_unordered_le (I N : Finset ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (M : ℕ) (hN : ∀ n ∈ N, n ≤ M)
    (w : ℕ → (I → Circle) → ℝ≥0∞) (hw : ∀ n ∈ N, Measurable (w n))
    (hprefix : ∀ n ∈ N,
      ∀ᵐ x ∂baseMeasure.withDensity (fun x : Base => w n (fun i : I => x i)),
        ∀ i ∈ I, circleRepresentative (x i) ≤
          circleRepresentative (rotationIterate θ (n : ℤ) x i)) :
    orbitAverageMeasure θ N (fun n x => w n (fun i : I => x i)) orderedPairEventᶜ ≤
      orbitAverageMeasure θ N (fun n x => w n (fun i : I => x i)) univ *
        (ENNReal.ofReal (M : ℝ) * ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal (θ i)) := by
  let B : ℝ≥0∞ := ENNReal.ofReal (M : ℝ) *
    ∑' i : {i : ℕ // i ∉ I}, ENNReal.ofReal (θ i)
  have hbound (n : ℕ) (hn : n ∈ N) :
      orbitPairMeasure θ n (fun x : Base => w n (fun i : I => x i)) orderedPairEventᶜ ≤
        orbitPairMeasure θ n (fun x : Base => w n (fun i : I => x i)) univ * B := by
    refine (orbitPairMeasure_unordered_le I θ hθ n (w n) (hw n hn) (hprefix n hn)).trans ?_
    apply mul_le_mul_right
    apply mul_le_mul_left
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hN n hn)
  change orbitAverageMeasure θ N (fun n x => w n (fun i : I => x i)) orderedPairEventᶜ ≤
    orbitAverageMeasure θ N (fun n x => w n (fun i : I => x i)) univ * B
  simp only [orbitAverageMeasure, Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply]
  rw [mul_assoc, Finset.sum_mul]
  apply mul_le_mul_right
  exact Finset.sum_le_sum hbound

theorem trimmed_orbitAverage_supported (θ : ℕ → ℝ) (N : Finset ℕ)
    (hN : ∀ n ∈ N, 0 < n) (w : ℕ → Base → ℝ≥0∞) :
    SupportedOnPositiveOrderedOrbitPairs θ
      ((orbitAverageMeasure θ N w).restrict orderedPairEvent) := by
  refine ⟨N, hN, ?_⟩
  have hm : MeasurableSet {xy : Base × Base |
      ∃ n ∈ N, xy.2 = rotationIterate θ (n : ℤ) xy.1} := by
    simp only [ofPred_exists]
    apply MeasurableSet.iUnion
    intro n
    by_cases hn : n ∈ N
    · simp only [hn, true_and]
      apply measurableSet_eq_fun measurable_snd
      apply Measurable.of_eval
      intro i
      exact ((measurable_pi_apply i).comp measurable_fst).add_const _
    · simp only [hn, false_and, ofPred_false, MeasurableSet.empty]
  have hgraph : ∀ᵐ xy ∂orbitAverageMeasure θ N w,
      ∃ n ∈ N, xy.2 = rotationIterate θ (n : ℤ) xy.1 := by
    apply Measure.ae_smul_measure
    apply ae_finsetSum_measure_iff.mpr
    intro n hn
    apply (ae_map_iff (measurable_orbitPairMap θ n).aemeasurable hm).mpr
    exact Filter.Eventually.of_forall (fun _ => ⟨n, hn, rfl⟩)
  filter_upwards [ae_restrict_mem measurableSet_orderedPairEvent,
    ae_restrict_of_ae hgraph] with xy horder hgraph
  exact ⟨horder, hgraph⟩

end Invariant233.ProductModel.TailTrimming

end

end OAI

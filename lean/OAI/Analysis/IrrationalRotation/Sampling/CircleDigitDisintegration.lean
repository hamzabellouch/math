import OAI.Analysis.IrrationalRotation.Couplings.CircleDigitCoupling

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

private lemma map_label_observe {D : Type*} [MeasurableSpace D]
    (ν : Measure (ℝ × ℝ)) [SFinite ν] (l : Label) (f : ℝ × ℝ → D) (hf : Measurable f) :
    (ν.map (fun z => (l, z))).map (fun z : CoordinateSample => (f z.2, z.1)) =
      (ν.map f).prod (Measure.dirac l) := by
  have hin : Measurable (fun z : ℝ × ℝ => (l, z)) := by fun_prop
  have hout : Measurable (fun z : CoordinateSample => (f z.2, z.1)) := by fun_prop
  rw [Measure.map_map hout hin, Measure.prod_dirac]
  rw [Measure.map_map (show Measurable (fun x : D => (x, l)) from by fun_prop) hf]
  rfl

private lemma observed_pair_left {D : Type*} [MeasurableSpace D]
    (ν η : Measure ℝ) [SFinite ν] [IsProbabilityMeasure η]
    (Q : ℝ → D) (hQ : Measurable Q) :
    (ν.prod η).map (fun z => Q z.1) = ν.map Q := by
  change (ν.prod η).map (Q ∘ Prod.fst) = _
  rw [← Measure.map_map hQ measurable_fst, Measure.map_fst_prod]
  simp

private lemma observed_pair_right {D : Type*} [MeasurableSpace D]
    (ν η : Measure ℝ) [IsProbabilityMeasure ν] [SFinite η]
    (Q : ℝ → D) (hQ : Measurable Q) :
    (ν.prod η).map (fun z => Q z.2) = η.map Q := by
  change (ν.prod η).map (Q ∘ Prod.snd) = _
  rw [← Measure.map_map hQ measurable_snd, Measure.map_snd_prod]
  simp

variable {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
include hm ha ha' hb hb'

lemma endpointLaw_ae_unit (side : Bool) (l : Label) :
    ∀ᵐ x ∂endpointLaw side m a b l, x ∈ Ico (0 : ℝ) 1 := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hinv : 1 / (2 * m) ≤ 1 := by apply (div_le_iff₀ (by linarith : 0 < 2 * m)).2; linarith
  have hinv0 : 0 < 1 / (2 * m) := one_div_pos.mpr (by linarith)
  cases l with
  | none => exact intervalLaw_ae_mem 0 1
  | some i =>
    cases side <;> fin_cases i <;> simp only [endpointLaw, Bool.false_eq_true, ite_false,
      ite_true, leftLaw, rightLaw]
    all_goals
      filter_upwards [intervalLaw_ae_mem _ _] with x hx
      constructor <;> linarith [hx.1, hx.2]

lemma endpointLaw_quantize_singleton (side : Bool) (r : ℕ) [NeZero r]
    (l : Label) (d : Fin r) :
    (endpointLaw side m a b l).map (UniformQuantization.quantize r) {d} =
      endpointLaw side m a b l (bin r d) := by
  rw [Measure.map_apply (UniformQuantization.measurable_quantize r) (measurableSet_singleton d)]
  apply measure_congr
  filter_upwards [endpointLaw_ae_unit hm ha ha' hb hb' side l] with x hx
  exact propext (UniformQuantization.quantize_eq_iff d hx)

lemma digitJoint_eq_sum (side : Bool) (r : ℕ) [NeZero r] :
    digitJoint side r κ m a b t =
      ∑ l, labelMass κ m a b t l •
        ((endpointLaw side m a b l).map (UniformQuantization.quantize r)).prod (Measure.dirac l) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have hQ := UniformQuantization.measurable_quantize r
  have hmap : Measurable (fun z : CoordinateSample =>
      (UniformQuantization.quantize r (endpoint side z), z.1)) := by
    cases side <;> dsimp [endpoint] <;> fun_prop
  unfold digitJoint rawLaw labelledMixture
  rw [Measure.map_add _ _ hmap, map_finsetSum _ _ hmap, Fintype.sum_option]
  simp only [Measure.map_smul _ hmap.aemeasurable]
  congr 1
  · cases side <;> simp only [endpoint, Bool.false_eq_true, ite_false, ite_true,
      labelMass, endpointLaw]
    all_goals
      first
      | rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) (by fun_prop)]
      | rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) (by fun_prop)]
      congr 2
      unfold CouplingMixture.diagonal
      have hdiag : Measurable (fun x : ℝ => (x, x)) := by fun_prop
      have hleft : Measurable (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) := by fun_prop
      have hright : Measurable (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) := by fun_prop
      first
      | rw [Measure.map_map hleft hdiag]
      | rw [Measure.map_map hright hdiag]
      rfl
  · apply Finset.sum_congr rfl
    intro i _
    cases side <;> simp only [endpoint, Bool.false_eq_true, ite_false, ite_true,
      labelMass, endpointLaw]
    · rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) (by fun_prop), observed_pair_left _ _ _ hQ]
    · rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) (by fun_prop), observed_pair_right _ _ _ hQ]

lemma digitJoint_singleton (side : Bool) (r : ℕ) [NeZero r]
    (d : Fin r) (l : Label) :
    digitJoint side r κ m a b t {(d, l)} = digitWeight side r κ m a b t l d := by
  rw [digitJoint_eq_sum hm ha ha' hb hb']
  have hs : ({(d, l)} : Set (Fin r × Label)) = {d} ×ˢ {l} := by ext z; simp
  rw [hs]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  classical
  simp only [Set.mem_singleton_iff, mul_ite, mul_zero, Set.indicator_apply]
  rw [Finset.sum_eq_single l]
  · rw [endpointLaw_quantize_singleton hm ha ha' hb hb']
    simp [digitWeight]
  · intro k _ hkl
    simp [hkl]
  · simp

lemma digitJoint_fst_singleton (side : Bool) (r : ℕ) [NeZero r] (d : Fin r) :
    (digitJoint side r κ m a b t).fst {d} =
      ∑ l, digitWeight side r κ m a b t l d := by
  rw [digitJoint_eq_sum hm ha ha' hb hb', Measure.fst,
    map_finsetSum _ _ measurable_fst]
  simp only [Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_fst_prod,
    measure_univ, one_smul,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [endpointLaw_quantize_singleton hm ha ha' hb hb']
  rfl

variable (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (ht0 : 0 ≤ t) (ht : t ≤ 1)
include hκ0 hκ ht0 ht

lemma labelsGivenDigit_disintegration (side : Bool) (r : ℕ) [NeZero r] :
    (digitJoint side r κ m a b t).fst ⊗ₘ labelsGivenDigit side r κ m a b t =
      digitJoint side r κ m a b t := by
  have := rawLaw_isProbabilityMeasure hκ0 hκ hm ha ha' hb hb' ht0 ht
  have : IsFiniteMeasure (digitJoint side r κ m a b t) := by
    unfold digitJoint
    infer_instance
  have := labelsGivenDigit_isMarkov hκ0 hκ hm ha ha' hb hb' ht0 ht side r
  apply Measure.ext_of_singleton
  rintro ⟨d, l⟩
  have hs : ({(d, l)} : Set (Fin r × Label)) = {d} ×ˢ {l} := by ext z; simp
  rw [hs, Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton]
  rw [labelsGivenDigit_singleton, digitJoint_fst_singleton hm ha ha' hb hb', ← hs,
    digitJoint_singleton hm ha ha' hb hb']
  exact ENNReal.div_mul_cancel
    (digitWeight_total_ne_zero hκ0 hκ hm ha ha' hb hb' ht0 ht side r d)
    (digitWeight_total_ne_top hm ha ha' hb hb' side r d)

end Invariant233.CircleDigitCoupling

end

end OAI

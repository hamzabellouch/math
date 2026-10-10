import OAI.Analysis.IrrationalRotation.Couplings.CircleCouplingCrossings

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMixture CouplingMarginalBounds OneCoordinateCoupling

lemma rawLaw_ae_of_components {κ m a b t : ℝ} {P : CoordinateSample → Prop}
    (hP : MeasurableSet {z | P z})
    (hdiag : ∀ᵐ x ∂baseLaw, P (none, (x, x)))
    (hcomp : ∀ i : Fin 5, ∀ᵐ z ∂(leftLaw (2 * m) a b i).prod (rightLaw (2 * m) a b i),
      P (some i, z)) : ∀ᵐ z ∂rawLaw κ m a b t, P z := by
  unfold rawLaw labelledMixture
  rw [ae_add_measure_iff, ae_finsetSum_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (show Measurable (fun z : ℝ × ℝ => ((none : Label), z)) from by fun_prop).aemeasurable hP).2
    unfold CouplingMixture.diagonal
    exact (ae_map_iff (show Measurable (fun x : ℝ => (x, x)) from by fun_prop).aemeasurable
      (show MeasurableSet {z : ℝ × ℝ | P (none, z)} from
        (show Measurable (fun z : ℝ × ℝ => ((none : Label), z)) from by fun_prop) hP)).2 hdiag
  · intro i _
    exact Measure.ae_smul_measure
      ((ae_map_iff (show Measurable (fun z : ℝ × ℝ => (some i, z)) from by fun_prop).aemeasurable hP).2 (hcomp i)) _

section Parameters
variable {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
include hm ha ha' hb hb'

lemma rawLaw_ae_endpoint_property (side : Bool) {P : Label → ℝ → Prop}
    (hP : MeasurableSet {z : CoordinateSample | P z.1 (endpoint side z)})
    (hbase : ∀ᵐ x ∂baseLaw, P none x)
    (hl : ∀ i : Fin 5, ∀ᵐ x ∂endpointLaw side m a b (some i), P (some i) x) :
    ∀ᵐ z ∂rawLaw κ m a b t, P z.1 (endpoint side z) := by
  have hm0 : 0 < m := by linarith
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  apply rawLaw_ae_of_components hP
  · cases side <;> exact hbase
  · intro i
    cases side
    · exact (measurePreserving_fst (μ := leftLaw (2 * m) a b i)
        (ν := rightLaw (2 * m) a b i)).quasiMeasurePreserving.ae (hl i)
    · exact (measurePreserving_snd (μ := leftLaw (2 * m) a b i)
        (ν := rightLaw (2 * m) a b i)).quasiMeasurePreserving.ae (hl i)

lemma rawLaw_ae_endpoint_unit (side : Bool) :
    ∀ᵐ z ∂rawLaw κ m a b t, endpoint side z ∈ Ico (0 : ℝ) 1 := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' side (P := fun _ x => x ∈ Ico (0 : ℝ) 1)
  · apply measurableSet_Ico.preimage
    cases side
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
  · exact intervalLaw_ae_mem 0 1
  · intro i
    exact endpointLaw_ae_unit hm ha ha' hb hb' side (some i)

lemma rawLaw_ae_top_support (which : Bool) :
    ∀ᵐ z ∂rawLaw κ m a b t, z.1 = topLabel which → 1 - width a b which / 2 ≤ z.2.2 := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' true (P := fun l x => l = topLabel which → 1 - width a b which / 2 ≤ x)
  · simp only [imp_iff_not_or, endpoint, ite_true]
    exact (measurableSet_eq_fun measurable_fst measurable_const).compl.union
      (measurableSet_le measurable_const (measurable_snd.comp measurable_snd))
  · exact Eventually.of_forall (by intro x h; cases which <;> cases h)
  · intro i
    by_cases hi : some i = topLabel which
    · cases which
      · have he : i = 0 := Option.some.inj hi
        subst i
        filter_upwards [intervalLaw_ae_mem (1 - a / 2) 1] with x hx
        exact fun _ => hx.1
      · have he : i = 2 := Option.some.inj hi
        subst i
        filter_upwards [intervalLaw_ae_mem (1 - b / 2) 1] with x hx
        exact fun _ => hx.1
    · exact Eventually.of_forall (fun _ h => (hi h).elim)

lemma rawLaw_ae_bottom_support (which : Bool) :
    ∀ᵐ z ∂rawLaw κ m a b t, z.1 = bottomLabel which → z.2.1 < width a b which / 2 := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' false (P := fun l x => l = bottomLabel which → x < width a b which / 2)
  · simp only [imp_iff_not_or, endpoint, Bool.false_eq_true, ite_false]
    exact (measurableSet_eq_fun measurable_fst measurable_const).compl.union
      (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const)
  · exact Eventually.of_forall (by intro x h; cases which <;> cases h)
  · intro i
    by_cases hi : some i = bottomLabel which
    · cases which
      · have he : i = 1 := Option.some.inj hi
        subst i
        filter_upwards [intervalLaw_ae_mem 0 (a / 2)] with x hx
        exact fun _ => hx.2
      · have he : i = 3 := Option.some.inj hi
        subst i
        filter_upwards [intervalLaw_ae_mem 0 (b / 2)] with x hx
        exact fun _ => hx.2
    · exact Eventually.of_forall (fun _ h => (hi h).elim)

end Parameters
end Invariant233.CircleDigitCoupling

end

end OAI

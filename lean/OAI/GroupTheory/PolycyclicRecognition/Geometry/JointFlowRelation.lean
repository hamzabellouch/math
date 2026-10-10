import OAI.GroupTheory.PolycyclicRecognition.Geometry.RationalFlowBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ContinuousFlowAffinity
import Mathlib.MeasureTheory.Group.Measure

namespace OAI

/-! # From intervalwise label agreement to agreement on all admissible segments -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory MeasureTheory.Measure

theorem measurableSet_flow_label_relation
    {G V L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Countable L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (Exp : V → G) (hExp : Continuous Exp) (v : V)
    (label : G → L) (hl : Measurable label) (R : L → L → Prop) :
    MeasurableSet {z : (ℝ × ℝ) × G |
      R (label (z.2 * Exp (z.1.1 • v))) (label (z.2 * Exp (z.1.2 • v)))} := by
  have hm : Measurable (fun z : (ℝ × ℝ) × G =>
      (label (z.2 * Exp (z.1.1 • v)), label (z.2 * Exp (z.1.2 • v)))) :=
    (hl.comp ((continuous_snd.mul (hExp.comp
      ((continuous_fst.comp continuous_fst).smul continuous_const))).measurable)).prodMk
      (hl.comp ((continuous_snd.mul (hExp.comp
        ((continuous_snd.comp continuous_fst).smul continuous_const))).measurable))
  exact hm ((Set.to_countable {p : L × L | R p.1 p.2}).measurableSet)

theorem ae_joint_flow_relation_of_intervals
    {G V L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Countable L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (μ : Measure G) [SFinite μ] [μ.IsMulRightInvariant]
    (Exp : V → G) (hExp : Continuous Exp)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : V) (U : Set G) (hU : IsOpen U)
    (label : G → L) (hl : Measurable label) (R : L → L → Prop)
    (hline : ∀ T : ℝ, 0 < T → ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∀ᵐ s ∂volume.restrict (Ioc 0 T), ∀ᵐ t ∂volume.restrict (Ioc 0 T),
        R (label (g * Exp (s • v))) (label (g * Exp (t • v)))) :
    ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      R (label (z.2 * Exp (z.1.1 • v))) (label (z.2 * Exp (z.1.2 • v))) := by
  have hRel := measurableSet_flow_label_relation Exp hExp v label hl R
  rw [flowSegmentDomain_eq_iUnion_rationalFlowBox U hU Exp hExp v,
    ae_restrict_iUnion_iff]
  rintro ⟨a, b⟩
  apply (ae_restrict_iff hRel).mpr
  by_cases hab : (a : ℝ) < b
  · let T : ℝ := b - a
    have hT : 0 < T := sub_pos.mpr hab
    let P : ((ℝ × ℝ) × G) → Prop := fun z =>
      z.1.1 ∈ Ioc 0 T → z.1.2 ∈ Ioc 0 T → z.2 ∈ flowLineBase U Exp v T →
        R (label (z.2 * Exp (z.1.1 • v))) (label (z.2 * Exp (z.1.2 • v)))
    have hP : MeasurableSet {z | P z} := by
      change MeasurableSet {z : (ℝ × ℝ) × G | z.1.1 ∈ Ioc 0 T →
        z.1.2 ∈ Ioc 0 T → z.2 ∈ flowLineBase U Exp v T →
        R (label (z.2 * Exp (z.1.1 • v))) (label (z.2 * Exp (z.1.2 • v)))}
      exact (measurableSet_Ioc.preimage (measurable_fst.comp measurable_fst)).imp
        ((measurableSet_Ioc.preimage (measurable_snd.comp measurable_fst)).imp
          (((isOpen_flowLineBase U hU Exp hExp v T).measurableSet.preimage
            measurable_snd).imp hRel))
    have hswap : ∀ᵐ z ∂μ.prod pairTimeMeasure, P (z.2, z.1) := by
      apply (ae_prod_iff_ae_ae (hP.preimage measurable_swap)).mpr
      filter_upwards [hline T hT] with g hg
      apply (ae_prod_iff_ae_ae ((hP.preimage (by fun_prop)))).mpr
      by_cases hstay : g ∈ flowLineBase U Exp v T
      · filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp (hg hstay)] with s hs
        by_cases hs' : s ∈ Ioc 0 T
        · filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp (hs hs')] with t ht
          exact fun _ ht' _ => ht ht'
        · exact Eventually.of_forall (fun _ hs'' => (hs' hs'').elim)
      · exact Eventually.of_forall (fun _ => Eventually.of_forall (fun _ _ _ hg' =>
          (hstay hg').elim))
    have hpair : ∀ᵐ z ∂pairTimeMeasure.prod μ, P z :=
      (measurePreserving_swap (μ := pairTimeMeasure) (ν := μ)).quasiMeasurePreserving.ae hswap
    have hshift : MeasurePreserving
        (fun z : (ℝ × ℝ) × G => ((z.1.1 - a, z.1.2 - a), z.2 * Exp ((a : ℝ) • v)))
        (pairTimeMeasure.prod μ) (pairTimeMeasure.prod μ) := by
      convert
        ((measurePreserving_add_right (volume : Measure ℝ) (-(a : ℝ))).prod
          (measurePreserving_add_right (volume : Measure ℝ) (-(a : ℝ)))).prod
          (measurePreserving_mul_right μ (Exp ((a : ℝ) • v))) using 1
      funext z
      simp only [Prod.map, sub_eq_add_neg]
      all_goals rfl
    filter_upwards [hshift.quasiMeasurePreserving.ae hpair] with z hz hzbox
    have hs : z.1.1 - a ∈ Ioc 0 T := by
      change 0 < z.1.1 - a ∧ z.1.1 - a ≤ (b : ℝ) - a
      constructor <;> linarith [hzbox.1.1, hzbox.1.2]
    have ht : z.1.2 - a ∈ Ioc 0 T := by
      change 0 < z.1.2 - a ∧ z.1.2 - a ≤ (b : ℝ) - a
      constructor <;> linarith [hzbox.2.1.1, hzbox.2.1.2]
    have hstay : z.2 * Exp ((a : ℝ) • v) ∈ flowLineBase U Exp v T := by
      intro t ht
      rw [mul_assoc, ← hadd]
      apply hzbox.2.2
      constructor <;> dsimp [T] at ht <;> linarith [ht.1, ht.2]
    have heq (t : ℝ) : z.2 * Exp ((a : ℝ) • v) * Exp ((t - a) • v) =
        z.2 * Exp (t • v) := by
      rw [mul_assoc, ← hadd]
      rw [show (a : ℝ) + (t - a) = t by ring]
    simpa only [P, heq] using hz hs ht hstay
  · exact Eventually.of_forall (fun z hz => (hab (hz.1.1.trans hz.1.2)).elim)

end PolycyclicRecognition

end

end OAI

import OAI.Dynamics.TriangleBilliards.ReflectedSmoothing

namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section
open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff
noncomputable section

/-! The actual oriented double of the billiard, in its full-measure pair of
interior charts. The second coordinate records the parity of reflections;
it is not an independent randomization of the dynamics. -/
namespace TriangularBilliards

open Function Filter
open scoped Topology

abbrev DoublePhase := Phase × ZMod 2

def parityMeasure : Measure (ZMod 2) := (2 : ℝ≥0∞)⁻¹ • Measure.count

instance parityMeasure_probability : IsProbabilityMeasure parityMeasure := by
  constructor
  simp only [parityMeasure, Measure.smul_apply, smul_eq_mul, Measure.count_univ, ENat.card_eq_coe_fintype_card, ZMod.card, ENat.toENNReal_coe]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

def doubleMeasure (Q : Triangle) : Measure DoublePhase := (phaseMeasure Q).prod parityMeasure

instance doubleMeasure_probability (Q : Triangle) : IsProbabilityMeasure (doubleMeasure Q) := by
  unfold doubleMeasure
  infer_instance

lemma measurePreserving_parity_add (a : ZMod 2) :
    MeasurePreserving (fun b => a + b) parityMeasure parityMeasure := by
  have h : MeasurePreserving (fun b : ZMod 2 => a + b) Measure.count Measure.count := by
    refine ⟨measurable_of_countable _, Measure.eq_of_le_of_measure_univ_eq ?_ ?_⟩
    · exact (add_right_injective a).map_count_le (measurable_of_countable _)
    · rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ, preimage_univ]
  exact h.smul_measure _

def collisionIndex (Q : Triangle) (t : ℝ) (z : Phase) : ℤ := by
  classical
  exact if Nonempty (FlightChain Q z) then CodedChain.index (CodedChain.fromPhase Q z, t) else 0

lemma collisionIndex_spec {Q : Triangle} {z : Phase} (c : FlightChain Q z) (t : ℝ) :
    c.time (collisionIndex Q t z) ≤ t ∧ t < c.time (collisionIndex Q t z + 1) := by
  classical
  let d : CodedChain Q := ⟨(z, c.data), c.data_valid⟩
  have he : CodedChain.fromPhase Q z = d := CodedChain.fromPhase_initial Q d
  have hc : d.chain = c := FlightChain.unique _ _
  simp only [collisionIndex, ite_eq_left (show Nonempty (FlightChain Q z) from ⟨c⟩), he]
  simpa only [hc] using CodedChain.index_spec (d, t)

lemma collisionIndex_eq {Q : Triangle} {z : Phase} (c : FlightChain Q z) {t : ℝ} {n : ℤ}
    (hn : c.time n ≤ t ∧ t < c.time (n + 1)) : collisionIndex Q t z = n :=
  c.flight_index_unique (collisionIndex_spec c t) hn

@[fun_prop] lemma measurable_collisionIndex (Q : Triangle) :
    Measurable (fun a : ℝ × Phase => collisionIndex Q a.1 a.2) := by
  classical
  apply Measurable.ite
  · exact (CodedChain.measurableSet_regular Q).preimage measurable_snd
  · exact (CodedChain.measurable_index Q).comp
      (((CodedChain.measurable_fromPhase Q).comp measurable_snd).prodMk measurable_fst)
  · exact measurable_const

lemma collisionIndex_zero (Q : Triangle) (z : Phase) : collisionIndex Q 0 z = 0 := by
  classical
  by_cases h : Nonempty (FlightChain Q z)
  · exact collisionIndex_eq h.some ⟨h.some.zero_before.le, h.some.zero_after⟩
  · simp [collisionIndex, h]

/-- Unit-speed geodesic flow of the oriented double in the two interior charts. -/
def doubleFlow (Q : Triangle) (t : ℝ) (z : DoublePhase) : DoublePhase :=
  (billiardFlow Q t z.1, (collisionIndex Q t z.1 : ZMod 2) + z.2)

@[fun_prop] lemma measurable_doubleFlow (Q : Triangle) :
    Measurable (fun a : ℝ × DoublePhase => doubleFlow Q a.1 a.2) := by
  have hi : Measurable (fun a : ℝ × DoublePhase => (collisionIndex Q a.1 a.2.1 : ZMod 2)) :=
    (measurable_of_countable (fun n : ℤ => (n : ZMod 2))).comp
      ((measurable_collisionIndex Q).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  exact ((measurable_billiardFlow Q).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
    (hi.add (measurable_snd.comp measurable_snd))

@[fun_prop] lemma measurable_doubleFlow_time (Q : Triangle) (t : ℝ) :
    Measurable (doubleFlow Q t) :=
  (measurable_doubleFlow Q).comp (measurable_const.prodMk measurable_id)

lemma measurePreserving_doubleFlow (Q : Triangle) (t : ℝ) :
    MeasurePreserving (doubleFlow Q t) (doubleMeasure Q) (doubleMeasure Q) := by
  apply (measurePreserving_billiardFlow Q t).skew_product
    (g := fun z b => (collisionIndex Q t z : ZMod 2) + b)
  · exact measurable_snd.comp (measurable_doubleFlow_time Q t)
  · exact Eventually.of_forall fun z => (measurePreserving_parity_add _).map_eq

lemma doubleFlow_zero (Q : Triangle) (z : DoublePhase) : doubleFlow Q 0 z = z := by
  simp [doubleFlow, billiardFlow_zero, collisionIndex_zero]

lemma collisionIndex_rebase {Q : Triangle} {z : Phase} (c : FlightChain Q z)
    (t s : ℝ) (hn : c.time (collisionIndex Q t z) < t) :
    collisionIndex Q s (billiardFlow Q t z) + collisionIndex Q t z =
      collisionIndex Q (s + t) z := by
  let n := collisionIndex Q t z
  let m := collisionIndex Q (s + t) z
  have hn' := (collisionIndex_spec c t).2
  let d := c.rebase t n ⟨hn, hn'⟩
  have hm := collisionIndex_spec c (s + t)
  have hd : d.time (m - n) ≤ s ∧ s < d.time (m - n + 1) := by
    change c.time (m - n + n) - t ≤ s ∧ s < c.time (m - n + 1 + n) - t
    rw [sub_add_cancel, show m - n + 1 + n = m + 1 by omega]
    constructor <;> linarith [hm.1, hm.2]
  rw [billiardFlow_eq_chain c t, collisionIndex_eq d hd]
  exact sub_add_cancel _ _

lemma doubleFlow_add_of_noncollision {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) (s t : ℝ) (ht : t ∉ range c.time) :
    doubleFlow Q (s + t) z = doubleFlow Q s (doubleFlow Q t z) := by
  have hn : c.time (collisionIndex Q t z.1) < t := lt_of_le_of_ne
    (collisionIndex_spec c t).1 (fun h => ht ⟨_, h⟩)
  apply Prod.ext
  · exact billiardFlow_add_of_noncollision c s t ht
  · change (_ : ZMod 2) + z.2 = _ + (_ + z.2)
    change (collisionIndex Q (s + t) z.1 : ZMod 2) + z.2 =
      (collisionIndex Q s (billiardFlow Q t z.1) : ZMod 2) + ((collisionIndex Q t z.1 : ZMod 2) + z.2)
    rw [← add_assoc, ← Int.cast_add, collisionIndex_rebase c t s hn]

lemma doubleFlow_cocycle (Q : Triangle) (s t : ℝ) :
    doubleFlow Q (s + t) =ᵐ[doubleMeasure Q] (doubleFlow Q s ∘ doubleFlow Q t) := by
  have h : ∀ᵐ z ∂doubleMeasure Q, z.1 ∈ regularAt Q t :=
    Measure.quasiMeasurePreserving_fst.ae (ae_regularAt Q t)
  filter_upwards [h] with z hz
  obtain ⟨c⟩ := hz.1
  exact doubleFlow_add_of_noncollision c s t (regularAt_noncollision hz c)

/-- Rotation in the oriented tangent circle; the negative copy has the
opposite physical rotation, exactly as in a conjugate Euclidean chart. -/
def doubleRotate (a : Circle) (z : DoublePhase) : DoublePhase :=
  ((z.1.1, (if z.2 = 0 then a else a⁻¹) * z.1.2), z.2)

@[fun_prop] lemma measurable_doubleRotate (a : Circle) : Measurable (doubleRotate a) := by
  have h : Measurable (fun b : ZMod 2 => if b = 0 then a else a⁻¹) := measurable_of_countable _
  exact (measurable_fst.fst.prodMk ((h.comp measurable_snd).mul measurable_fst.snd)).prodMk measurable_snd

lemma measurePreserving_doubleRotate (Q : Triangle) (a : Circle) :
    MeasurePreserving (doubleRotate a) (doubleMeasure Q) (doubleMeasure Q) := by
  have h : MeasurePreserving
      (fun z : ZMod 2 × Phase => (z.1, (z.2.1, (if z.1 = 0 then a else a⁻¹) * z.2.2)))
      (parityMeasure.prod (phaseMeasure Q)) (parityMeasure.prod (phaseMeasure Q)) := by
    apply (MeasurePreserving.id parityMeasure).skew_product
      (g := fun (b : ZMod 2) (z : Phase) => (z.1, (if b = 0 then a else a⁻¹) * z.2))
    · have hm : Measurable (fun b : ZMod 2 => if b = 0 then a else a⁻¹) := measurable_of_countable _
      exact measurable_snd.fst.prodMk ((hm.comp measurable_fst).mul measurable_snd.snd)
    · exact Eventually.of_forall fun b =>
        ((MeasurePreserving.id ((volume Q.table)⁻¹ • volume.restrict Q.table)).prod
          (measurePreserving_circle_mul (if b = 0 then a else a⁻¹))).map_eq
  exact Measure.measurePreserving_swap.comp (h.comp Measure.measurePreserving_swap)

lemma doubleRotate_one (z : DoublePhase) : doubleRotate 1 z = z := by
  simp [doubleRotate]

lemma doubleRotate_mul (a b : Circle) (z : DoublePhase) :
    doubleRotate (a * b) z = doubleRotate a (doubleRotate b z) := by
  by_cases hz : z.2 = 0 <;> simp [doubleRotate, hz, mul_assoc, mul_comm b⁻¹ a⁻¹]

lemma doubleFlow_on_flight {Q : Triangle} {z : DoublePhase} (c : FlightChain Q z.1)
    {t : ℝ} {n : ℤ} (ht : c.time n ≤ t ∧ t < c.time (n + 1)) :
    doubleFlow Q t z =
      ((c.point n + (t - c.time n) • (c.direction n : ℂ), c.direction n),
        (n : ZMod 2) + z.2) := by
  simp only [doubleFlow, billiardFlow_eq_chain c t, c.at_of_flight ht, collisionIndex_eq c ht]

lemma continuousAt_doubleFlow_of_noncollision {Q : Triangle} {z : DoublePhase}
    (c : FlightChain Q z.1) {t : ℝ} (ht : t ∉ range c.time) :
    ContinuousAt (fun s => doubleFlow Q s z) t := by
  let n := collisionIndex Q t z.1
  have hn : t ∈ Ioo (c.time n) (c.time (n + 1)) :=
    ⟨lt_of_le_of_ne (collisionIndex_spec c t).1 (fun h => ht ⟨_, h⟩),
      (collisionIndex_spec c t).2⟩
  have he : (fun s => doubleFlow Q s z) =ᶠ[𝓝 t]
      (fun s => ((c.point n + (s - c.time n) • (c.direction n : ℂ), c.direction n),
        (n : ZMod 2) + z.2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hn] with s hs
    exact doubleFlow_on_flight c ⟨hs.1.le, hs.2⟩
  have hc : ContinuousAt
      (fun s : ℝ => ((c.point n + (s - c.time n) • (c.direction n : ℂ), c.direction n),
        (n : ZMod 2) + z.2)) t := by fun_prop
  exact hc.congr_of_eventuallyEq he

lemma ae_continuousAt_doubleFlow (Q : Triangle) (t : ℝ) :
    ∀ᵐ z ∂doubleMeasure Q, ContinuousAt (fun s => doubleFlow Q s z) t := by
  have h : ∀ᵐ z ∂doubleMeasure Q, z.1 ∈ regularAt Q t :=
    Measure.quasiMeasurePreserving_fst.ae (ae_regularAt Q t)
  filter_upwards [h] with z hz
  obtain ⟨c⟩ := hz.1
  exact continuousAt_doubleFlow_of_noncollision c (regularAt_noncollision hz c)

end TriangularBilliards

end
end

end OAI

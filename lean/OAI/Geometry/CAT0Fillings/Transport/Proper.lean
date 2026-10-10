import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.GeneralPush

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open Foundations CurrentOperations

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
lemma mass_push_one_general {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {f : X → Y} (hf : LipschitzWith 1 f) : mass (pushCurrent f T) ≤ mass T := by
  apply le_csInf
  · obtain ⟨μ,hμ,hc⟩ := hT.finiteMass
    exact ⟨μ.real univ,μ,hμ,hc,rfl⟩
  · rintro r ⟨μ,hμ,hc,rfl⟩
    let := hμ
    have hh := pushCurrent_controls hT hc hf
    simp only [one_pow,ENNReal.coe_one,one_smul] at hh
    have hl := mass_le_measure (T := pushCurrent f T) (μ := μ.map f) inferInstance hh
    simpa only [Measure.real,Measure.map_apply hf.continuous.measurable MeasurableSet.univ,
      preimage_univ] using hl

omit [MeasurableSpace X] [BorelSpace X] in
lemma IntegerChart.image_bounded {k : ℕ} (C : IntegerChart X k) : Bornology.IsBounded C.image := by
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨R,hR⟩ := Metric.isBounded_iff.mp C.bounded
  apply Metric.isBounded_iff.mpr
  refine ⟨(L:ℝ)*R,?_⟩
  rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩
  exact (hL.dist_le_mul a b).trans (mul_le_mul_of_nonneg_left
    (hR a.property b.property) L.coe_nonneg)

lemma IntegerChart.push_integerRectifiable_proper [ProperSpace X] [Nonempty X]
    [CompactSpace Y] [Nonempty Y] {k : ℕ} (C : IntegerChart X k)
    {f : X → Y} (hf : LipschitzWith 1 f) : IntegerRectifiable (pushCurrent f C.action) := by
  classical
  let o : X := Classical.choice inferInstance
  obtain ⟨R,hR,him⟩ := C.image_bounded.subset_closedBall_lt 0 o
  let B := closedBall o R
  have : Nonempty B := ⟨o,by simp [B,hR.le]⟩
  let D : IntegerChart B k := {
    domain := C.domain
    borel := C.borel
    bounded := C.bounded
    param := fun z => ⟨C.param z,him ⟨z,rfl⟩⟩
    bilipschitz := by
      obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
      exact ⟨L,U,hL,hU⟩
    multiplicity := C.multiplicity
    integrable := C.integrable }
  have hinc : LipschitzWith 1 (Subtype.val : B → X) := LipschitzWith.subtype_val B
  have heq : C.action = pushCurrent (Subtype.val : B → X) D.action := by
    funext b π
    by_cases hab : Admissible b π
    · rw [pushCurrent_apply _ _ hab,IntegerChart.action,ite_eq_left hab,
        IntegerChart.action,ite_eq_left (admissible_comp hab hinc)]
      rfl
    · simp only [IntegerChart.action,pushCurrent,ite_eq_right hab]
  rw [heq,←pushCurrent_comp hf]
  exact D.push_integerRectifiable D.action_isMetricCurrent (hf.comp hinc)

lemma integerRectifiable_push_proper [ProperSpace X] [Nonempty X]
    [CompactSpace Y] [Nonempty Y] {k : ℕ} {T : Functional X k} (hT : IntegerRectifiable T)
    {f : X → Y} (hf : LipschitzWith 1 f) : IntegerRectifiable (pushCurrent f T) := by
  classical
  obtain ⟨C,hd,hC,hCS,heq⟩ := hT
  have hP i : IsMetricCurrent (pushCurrent f (C i).action) := pushCurrent_isMetricCurrent (hC i) hf
  have hPI i : IntegerRectifiable (pushCurrent f (C i).action) := (C i).push_integerRectifiable_proper hf
  have hPS : Summable (fun i => mass (pushCurrent f (C i).action)) :=
    hCS.of_nonneg_of_le (fun i => mass_nonneg _) (fun i => mass_push_one_general (hC i) hf)
  have hEq : pushCurrent f T = (fun b π => ∑' i, pushCurrent f (C i).action b π) := by
    funext b π
    by_cases hab : Admissible b π
    · simp_rw [pushCurrent_apply f _ hab]
      exact heq _ _
    · simp only [pushCurrent,ite_eq_right hab,tsum_zero]
  rw [hEq]
  exact integerRectifiable_tsum hP hPI hPS
lemma integral_push_proper [ProperSpace X] [Nonempty X]
    [CompactSpace Y] [Nonempty Y] {k : ℕ} {T : Functional X k} (hT : IsIntegral k T)
    {f : X → Y} (hf : LipschitzWith 1 f) : IsIntegral k (pushCurrent f T) := by
  cases k with
  | zero => exact ⟨pushCurrent_isMetricCurrent hT.1 hf,integerRectifiable_push_proper hT.2 hf⟩
  | succ k =>
    refine ⟨pushCurrent_isMetricCurrent hT.1 hf,integerRectifiable_push_proper hT.2.1 hf,?_,?_⟩
    · rw [pushCurrent_boundarySucc T hf]
      exact pushCurrent_isMetricCurrent hT.2.2.1 hf
    · rw [pushCurrent_boundarySucc T hf]
      exact integerRectifiable_push_proper hT.2.2.2 hf
end CAT0Fillings
end

end OAI

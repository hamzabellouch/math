import Mathlib
import OAI.Probability.Ballisticity.Crossings.FirstHitPairGap
import OAI.Probability.Ballisticity.Estimates.FirstHighRecord

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma recordIndexPosition_suffix {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hD : X ∈ NoDrop ℓ 0) (ht : X ∈ TransientPaths ℓ) {n : ℕ} (hn : 0 < n)
    (htrue : TrueRecord ℓ X n) (j : ℕ) :
    recordIndexPosition ℓ (j+recordCount ℓ X n) X =
      recordIndexPosition ℓ j (fun k => X (n+k)-X n)+X n := by
  let Z : Path d := fun k => X (n+k)-X n
  have hpre : X ∈ RecordIndexPrefix ℓ (recordCount ℓ X n) n :=
    ⟨hn,htrue.1,rfl,fun k _ => hD k⟩
  have hzD : Z ∈ NoDrop ℓ 0 := (suffix_noDrop_iff ℓ X n).mpr htrue.2
  have hzt : Z ∈ TransientPaths ℓ := by
    change (fun k => X (n+k)) ∈ (fun Y : Path d => fun k => Y k-X n) ⁻¹' TransientPaths ℓ
    rw [transientPaths_translation]
    change Tendsto (fun k => dot (realPosition (X (n+k))) ℓ) atTop atTop
    have hh := (tendsto_add_atTop_iff_nat n).mpr ht
    simpa only [Nat.add_comm] using hh
  by_cases hj : j = 0
  · subst j
    rw [zero_add,recordIndexPosition,recordIndexTime_eq ℓ _ n X hpre,
      recordIndexPosition,recordIndexTime_zero]
    simp
  · obtain ⟨m,hm,hrec,hcount⟩ := exists_record_at_index ℓ Z hzt (Nat.pos_of_ne_zero hj)
    have hR : Z ∈ RecordIndexPrefix ℓ j m := ⟨hm,hrec,hcount,fun k _ => hzD k⟩
    have ha : X ∈ RecordIndexPrefix ℓ (j+recordCount ℓ X n) (n+m) := by
      refine ⟨by omega,(strictRecord_suffix_iff ℓ X htrue.1 hm).mp hrec,?_,fun k _ => hD k⟩
      rw [recordCount_add ℓ X htrue.1,hcount,Nat.add_comm]
    rw [recordIndexPosition,recordIndexTime_eq ℓ _ (n+m) X ha,
      recordIndexPosition,recordIndexTime_eq ℓ j m Z hR]
    exact (sub_add_cancel _ _).symm

noncomputable def highRecordCount {d : ℕ} (ℓ : Vector d) (J : ℝ) (X : Path d) : ℕ :=
  recordCount ℓ X (highWord ℓ J X).length

lemma measurable_highRecordCount {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) :
    Measurable (highRecordCount ℓ J) := by
  have h₁ : Measurable (fun p : Path d × ℕ => recordCount ℓ p.1 p.2) :=
    measurable_from_prod_countable_left (fun n => measurable_recordCount ℓ n)
  have h₂ : Measurable (fun X : Path d => (X, (highWord ℓ J X).length)) :=
    measurable_id.prodMk ((measurable_of_countable List.length).comp (measurable_highWord ℓ J hJ))
  change Measurable ((fun p : Path d × ℕ => recordCount ℓ p.1 p.2) ∘
    (fun X : Path d => (X, (highWord ℓ J X).length)))
  exact h₁.comp h₂

noncomputable def highRecordPosition {d : ℕ} (ℓ : Vector d) (J : ℝ) (X : Path d) : Lattice d :=
  X (highWord ℓ J X).length

lemma measurable_highRecordPosition {d : ℕ} (ℓ : Vector d) (J : ℝ) (hJ : 0 ≤ J) :
    Measurable (highRecordPosition ℓ J) := by
  exact (measurable_from_prod_countable_left (f := fun p : Path d × ℕ => p.1 p.2)
    (fun n => measurable_pi_apply n)).comp
      (measurable_id.prodMk ((measurable_of_countable List.length).comp (measurable_highWord ℓ J hJ)))

lemma conditioned_highSuffix_recordPosition {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (J : ℝ) (hJ : 0 ≤ J) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ j,
      recordIndexPosition ℓ j (highSuffix ℓ J X) =
        recordIndexPosition ℓ (j+highRecordCount ℓ J X) X-highRecordPosition ℓ J X := by
  filter_upwards [conditioned_highWord_exists ν ℓ htrans J,
    (conditionedLaw_absolutelyContinuous ν ℓ).ae_le htrans] with X hw ht j
  obtain ⟨w,hw⟩ := hw
  have hne : w ≠ [] := by
    intro h
    rw [h,highWordEvent_nil ℓ J hJ] at hw
    exact hw
  have he := (highWord_eq_iff ℓ J X w hne).mpr hw
  have hn : 0 < w.length := List.length_pos_iff.mpr hne
  have hh := recordIndexPosition_suffix ℓ X hw.1 ht hn hw.2.2.1 j
  have hPos : highRecordPosition ℓ J X = X w.length := by simp only [highRecordPosition,he]
  have hCnt : highRecordCount ℓ J X = recordCount ℓ X w.length := by simp only [highRecordCount,he]
  have hS : highSuffix ℓ J X = fun k => X (w.length+k)-X w.length := by
    funext k
    change X ((highWord ℓ J X).length+k)-X (highWord ℓ J X).length = _
    rw [he]
  rw [hCnt,hPos,hS,hh,add_sub_cancel_right]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI

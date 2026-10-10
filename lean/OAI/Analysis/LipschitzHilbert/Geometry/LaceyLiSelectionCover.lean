import OAI.Analysis.LipschitzHilbert.Geometry.PositiveRectangleAuxiliary
import OAI.Analysis.LipschitzHilbert.Geometry.RectangleCoverSelection

namespace OAI

/-! The actual discarded-family covering estimate in the Lacey--Li
selection algorithm. The remaining energy estimate is geometric. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
variable {ι κ : Type*} [Fintype κ]

theorem rectangleCount_mono (R : ι → Rectangle) {s t : Finset ι} (h : s ⊆ t) :
    rectangleCount R s ≤ rectangleCount R t := by
  intro x
  exact Finset.sum_le_sum_of_subset h

def maximalBlocked (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle)
    (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) (s : Finset ι) (i : ι) : Prop :=
  (R i).carrier ⊆ {x | η < positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a ha) s) x}

theorem maximalBlocked_mono (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle)
    (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) {s t : Finset ι} (hst : s ⊆ t) (i : ι)
    (hi : maximalBlocked e R a ha η s i) : maximalBlocked e R a ha η t i := by
  intro x hx
  exact (hi hx).trans_le (positiveAuxiliary_mono e (rectangleCount_mono _ hst) x)

theorem not_maximalBlocked_empty (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle)
    (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) (i : ι) : ¬maximalBlocked e R a ha η ∅ i := by
  intro h
  have hc : (R i).center ∈ (R i).carrier := by
    constructor <;> simp only [sub_self,map_zero,PiLp.zero_apply,abs_zero] <;>
      linarith [(R i).short_pos,(R i).long_pos]
  have hh := h hc
  change η < positiveAuxiliary e (rectangleCount (fun j => (R j).dilate a ha) ∅) (R i).center at hh
  have hz : rectangleCount (fun j => (R j).dilate a ha) ∅ = fun _ => 0 := by
    funext x
    simp [rectangleCount]
  rw [hz,positiveAuxiliary_zero] at hh
  exact not_lt_zero hh

theorem rectangle_cover_run_maximal_exists [DecidableEq ι]
    (e : κ → Plane ≃ᵐ (ℝ × ℝ)) (R : ι → Rectangle)
    (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞) (stock : Finset ι) :
    ∃ selected, RectangleCoverRun R (maximalBlocked e R a ha η) ∅ stock selected :=
  rectangle_cover_run_exists R (maximalBlocked e R a ha η) stock ∅
    (fun i _ => not_maximalBlocked_empty e R a ha η i)

theorem maximal_selection_cover_bound [DecidableEq ι]
    (e : κ → Plane ≃ᵐ (ℝ × ℝ))
    (he : ∀ i, MeasurePreserving (e i) volume (volume.prod volume))
    (R : ι → Rectangle) (a : ℝ) (ha : 0 < a) (η : ℝ≥0∞)
    (hη : η ≠ 0) (hηtop : η ≠ ∞) (stock : Finset ι) (selected : List ι)
    (hrun : RectangleCoverRun R (maximalBlocked e R a ha η) ∅ stock selected) :
    volume (⋃ i ∈ stock, (R i).carrier) ≤
      (1 + (9 + 3 * Fintype.card κ) * η⁻¹ * ENNReal.ofReal (a^2)) *
        ∑ i ∈ selected.toFinset, volume (R i).carrier := by
  let count := rectangleCount (fun i => (R i).dilate a ha) selected.toFinset
  let E := {x | η < positiveAuxiliary e count x}
  have hb : ∀ i ∈ stock, i ∉ selected → (R i).carrier ⊆ E := by
    intro i hi hnot
    have h := hrun.rejected_blocked
      (fun s t hst i hi => maximalBlocked_mono e R a ha η hst i hi) i hi hnot
    simpa only [Finset.empty_union,maximalBlocked] using h
  have hsub : (⋃ i ∈ stock, (R i).carrier) ⊆
      (⋃ i ∈ selected.toFinset, (R i).carrier) ∪ E := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
    by_cases hs : i ∈ selected
    · exact Or.inl (mem_iUnion₂.mpr ⟨i,List.mem_toFinset.mpr hs,hxi⟩)
    · exact Or.inr (hb i hi hs hxi)
  have hmass : (∫⁻ x, count x) = ENNReal.ofReal (a^2) *
      ∑ i ∈ selected.toFinset, volume (R i).carrier := by
    rw [rectangleCount_first_moment]
    simp_rw [Rectangle.volume_dilate]
    rw [Finset.mul_sum]
  have hweak := positiveAuxiliary_weak_L1 e he
    (rectangleCount_measurable (fun i : ι => (R i).dilate a ha) selected.toFinset) η hη hηtop
  change volume E ≤ _ at hweak
  rw [hmass] at hweak
  calc
    _ ≤ volume ((⋃ i ∈ selected.toFinset, (R i).carrier) ∪ E) := measure_mono hsub
    _ ≤ volume (⋃ i ∈ selected.toFinset, (R i).carrier) + volume E := measure_union_le _ _
    _ ≤ (∑ i ∈ selected.toFinset, volume (R i).carrier) +
        (9 + 3 * Fintype.card κ) * η⁻¹ * (ENNReal.ofReal (a^2) *
        ∑ i ∈ selected.toFinset, volume (R i).carrier) :=
      add_le_add (measure_biUnion_finset_le _ _) hweak
    _ = _ := by ring

end LipschitzHilbert

end

end OAI

import Mathlib
import OAI.Analysis.HardSphere.Geometry.LocalCheck

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {ι C : Type*} [Fintype ι] [Fintype C] [DecidableEq ι]
  {X : ι → Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype ι] in
lemma uniformInsertion_of_check_failures (checks : C → LocalCheck X)
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (p : ι → C → ℝ≥0∞) (a : ℝ≥0∞)
    (hfail : ∀i c, i∈(checks c).support → ∀x : ∀j,X j,
      μ i {y | ¬(checks c).pass (Function.update x i y)} ≤ p i c)
    (htotal : ∀i,a+(∑c∈Finset.univ.filter (fun c ↦ i∈(checks c).support),p i c) ≤ 1) :
    UniformInsertion checks μ a := by
  classical
  intro s i hi x
  let B : Set (X i) := {y | Function.update x i y ∈ insertionEvent checks s i}
  have hm : Measurable (fun y : X i ↦ Function.update x i y) := by
    fun_prop
  have hB : MeasurableSet B := (measurableSet_insertionEvent checks s i).preimage hm
  have hsub : Bᶜ ⊆ ⋃c∈Finset.univ.filter (fun c ↦ i∈(checks c).support),
      {y | ¬(checks c).pass (Function.update x i y)} := by
    intro y hy
    classical
    simp only [B,Set.mem_compl_iff,Set.mem_ofPred_eq,insertionEvent] at hy
    push Not at hy
    rcases hy with ⟨c,hc,hcs,hp⟩
    have hci : i∈(checks c).support := by
      by_contra hn
      apply hcs
      intro j hj
      have h := hc hj
      rcases Finset.mem_insert.mp h with he|hs
      · subst j; contradiction
      · exact hs
    exact mem_iUnion.2 ⟨c,mem_iUnion.2 ⟨by simp [hci],hp⟩⟩
  have hb : μ i Bᶜ ≤ ∑c∈Finset.univ.filter (fun c ↦ i∈(checks c).support),p i c := by
    apply (measure_mono hsub).trans
    apply (measure_biUnion_finset_le _ _).trans
    exact Finset.sum_le_sum fun c hc ↦ hfail i c (Finset.mem_filter.mp hc).2 x
  have hadd : a+μ i Bᶜ ≤ μ i B+μ i Bᶜ := by
    rw [measure_add_measure_compl hB]
    exact (add_le_add_right hb a).trans (by simpa using htotal i)
  have ha : a≤μ i B := (ENNReal.add_le_add_iff_right (measure_ne_top _ _)).mp hadd
  have he : (fun y ↦ (insertionEvent checks s i).indicator (fun _ ↦ (1 : ℝ≥0∞)) (Function.update x i y))=
      B.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by funext y; simp [B,Set.indicator_apply]
  rw [he,lintegral_indicator hB]
  simpa using ha

end HardSphere.Comparison

end
end

end

end OAI

import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.PatchResponse

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

theorem finite_inverse_mesh_event {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (P : @Measure Ω m₀) [IsFiniteMeasure P] (t : Finset Position) (heights : Finset ℝ)
    (cnt : Ω → ℝ) (d u : Ω → Position → ℝ) {K η p : ℝ}
    (hc : Measurable[m] cnt) (hd : ∀ y,Measurable[m] (fun a => d a y))
    (hu : ∀ y,Measurable[m] (fun a => u a y))
    (hp : ∀ y∈t,∀ h∈heights,
      P.real {a | cnt a ≤ K ∧ Coulomb.tfScalarDensity h ≤ d a y ∧ u a y ≤ h-η} ≤ p ∧
      P.real {a | cnt a ≤ K ∧ d a y ≤ Coulomb.tfScalarDensity h ∧ h+η ≤ u a y} ≤ p) :
    ∃ G : Set Ω,(MeasurableSet[m₀] G ∧ MeasurableSet[m] G) ∧
      P.real Gᶜ ≤ 2*(t.card:ℝ)*(heights.card:ℝ)*p ∧
      ∀ a∈G,cnt a ≤ K → ∀ y∈t,∀ h∈heights,
        (Coulomb.tfScalarDensity h ≤ d a y → h-η < u a y) ∧
        (d a y ≤ Coulomb.tfScalarDensity h → u a y < h+η) := by
  let B := fun q : Position × ℝ =>
    {a | cnt a ≤ K ∧ Coulomb.tfScalarDensity q.2 ≤ d a q.1 ∧ u a q.1 ≤ q.2-η} ∪
    {a | cnt a ≤ K ∧ d a q.1 ≤ Coulomb.tfScalarDensity q.2 ∧ q.2+η ≤ u a q.1}
  let s := t.product heights
  have hBm (q : Position × ℝ) : MeasurableSet[m] (B q) := by
    exact ((measurableSet_le hc measurable_const).inter
      ((measurableSet_le measurable_const (hd q.1)).inter (measurableSet_le (hu q.1) measurable_const))).union
      ((measurableSet_le hc measurable_const).inter
        ((measurableSet_le (hd q.1) measurable_const).inter (measurableSet_le measurable_const (hu q.1))))
  let E := ⋃ q∈s,B q
  have hEm : MeasurableSet[m] E := MeasurableSet.biUnion (s.finite_toSet.countable) (fun q _ => hBm q)
  refine ⟨Eᶜ,⟨hm _ hEm.compl,hEm.compl⟩,?_,?_⟩
  · rw [compl_compl]
    calc
      P.real E ≤ ∑ q∈s,P.real (B q) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ q∈s,(2*p) := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hq0,hq1⟩ := Finset.mem_product.mp hq
        have H := hp q.1 hq0 q.2 hq1
        exact (measureReal_union_le _ _).trans (by linarith)
      _ = 2*(t.card:ℝ)*(heights.card:ℝ)*p := by simp [s]; ring
  · intro a ha hcnt y hy h hh
    have hnot : a∉B (y,h) := by
      intro hab
      exact ha (mem_iUnion.mpr ⟨(y,h),mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hy,hh⟩,hab⟩⟩)
    constructor
    · intro hden
      by_contra H
      exact hnot (Or.inl ⟨hcnt,hden,le_of_not_gt H⟩)
    · intro hden
      by_contra H
      exact hnot (Or.inr ⟨hcnt,hden,le_of_not_gt H⟩)
end NeutralAtom
end

end

end OAI

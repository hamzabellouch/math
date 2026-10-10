import Mathlib
import OAI.Geometry.PrescribedPotential.WirtingerCalculus

namespace OAI

/-! Compact Integral Propagation. -/

section

 

noncomputable section
open Set MeasureTheory
namespace PotentialABP
variable {X I : Type*} [TopologicalSpace X] [ConnectedSpace X]
  [MeasurableSpace X] [Fintype I]

 

omit [TopologicalSpace X] [ConnectedSpace X] in
lemma exists_le_total_div (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : Integrable u μ) (hn : ∀ x, 0 ≤ u x)
    {s : Set X} (hs : 0 < μ.real s) {B : ℝ} (hB : ∫ x, u x ∂μ ≤ B) :
    ∃ x ∈ s, u x ≤ B / μ.real s := by
  have hs0 : μ s ≠ 0 := by
    intro h; simp [measureReal_def, h] at hs
  obtain ⟨x, hx, hv⟩ := exists_le_setAverage hs0 (measure_ne_top μ s) hu.integrableOn
  refine ⟨x, hx, hv.trans ?_⟩
  rw [setAverage_eq, smul_eq_mul, ← div_eq_inv_mul]
  apply div_le_div_of_nonneg_right _ hs.le
  exact (setIntegral_le_integral hu (Filter.Eventually.of_forall hn)).trans hB

 

theorem finite_cover_integral_bound
    (U : I → Set X) (hopen : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) (hcover : ∀ x, ∃ i, x ∈ U i)
    (μ : I → Measure X) [∀ i, IsFiniteMeasure (μ i)]
    (hover : ∀ i j, (U i ∩ U j).Nonempty → 0 < (μ i).real (U j))
    (F : (X → ℝ) → Prop)
    (hn : ∀ u, F u → ∀ x, 0 ≤ u x)
    (hint : ∀ u, F u → ∀ i, Integrable u (μ i))
    (C : I → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hlocal : ∀ u, F u → ∀ i y, y ∈ U i →
      (∫ x, u x ∂μ i) ≤ C i * (u y + 1)) :
    ∃ B : ℝ, ∀ u, F u → (∃ x, u x = 0) → ∀ i,
      (∫ x, u x ∂μ i) ≤ B := by
  classical
  have hstart (s : I) : ∀ j, ∃ B : ℝ, ∀ u, F u →
      (∃ x ∈ U s, u x = 0) → (∫ x, u x ∂μ j) ≤ B := by
    let Good : I → Prop := fun j => ∃ B : ℝ, ∀ u, F u →
      (∃ x ∈ U s, u x = 0) → (∫ x, u x ∂μ j) ≤ B
    have hGs : Good s := by
      refine ⟨C s, ?_⟩
      rintro u hu ⟨x, hx, hz⟩
      simpa [hz] using hlocal u hu s x hx
    have hstep {i j : I} (hi : Good i) (hij : (U i ∩ U j).Nonempty) : Good j := by
      obtain ⟨B, hB⟩ := hi
      refine ⟨C j * (B / (μ i).real (U j) + 1), ?_⟩
      intro u hu hz
      obtain ⟨y, hy, hyB⟩ := exists_le_total_div (μ i) (hint u hu i)
        (hn u hu) (hover i j hij) (hB u hu hz)
      exact (hlocal u hu j y hy).trans
        (mul_le_mul_of_nonneg_left (by linarith : u y + 1 ≤ B / (μ i).real (U j) + 1) (hC j))
    let V : Set X := ⋃ i, ⋃ (_ : Good i), U i
    have hVo : IsOpen V := isOpen_iUnion fun i => isOpen_iUnion fun _ => hopen i
    have hVc : IsClosed V := by
      have he : Vᶜ = ⋃ i, ⋃ (_ : ¬ Good i), U i := by
        ext x
        simp only [V, mem_compl_iff, mem_iUnion]
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := hcover x
          exact ⟨i, fun hg => hx ⟨i, hg, hi⟩, hi⟩
        · rintro ⟨i, hgi, hxi⟩ ⟨j, hgj, hxj⟩
          exact hgi (hstep hgj ⟨x, hxj, hxi⟩)
      apply isOpen_compl_iff.mp
      rw [he]
      exact isOpen_iUnion fun i => isOpen_iUnion fun _ => hopen i
    have hV : V = univ := (show IsClopen V from ⟨hVc, hVo⟩).eq_univ (by
      obtain ⟨x, hx⟩ := hne s
      exact ⟨x, mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨hGs, hx⟩⟩⟩)
    intro j
    obtain ⟨x, hx⟩ := hne j
    have hxV : x ∈ V := by rw [hV]; trivial
    obtain ⟨i, hgi, hxi⟩ := (by simpa only [V, mem_iUnion] using hxV :
      ∃ i, ∃ _ : Good i, x ∈ U i)
    exact hstep hgi ⟨x, hxi, hx⟩
  choose B hB using hstart
  refine ⟨∑ s, ∑ j, max (B s j) 0, ?_⟩
  intro u hu hz i
  obtain ⟨x, hx⟩ := hz
  obtain ⟨s, hs⟩ := hcover x
  apply (hB s i u hu ⟨x, hs, hx⟩).trans
  apply (le_max_left _ _).trans
  apply (Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ i)).trans
  exact Finset.single_le_sum (fun s _ => Finset.sum_nonneg fun j _ => le_max_right _ _)
    (Finset.mem_univ s)
end PotentialABP

end
end

end OAI

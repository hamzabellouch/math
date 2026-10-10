import OAI.Geometry.SurfaceImmersion.Geometry.FiniteCurveLocalDefiners

namespace OAI

/-! Finite closed boundary families can be isolated locally after any
continuous parametrization; no global extension of their coordinate maps
is needed. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma finite_boundary_local_definers {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (C : ι → Set X) (hC : ∀ i, IsClosed (C i)) (f : Base → X)
    {K P : Set Base} (hf : ∀ p ∈ K, ContinuousAt f p)
    (hcover : ∀ p ∈ K, ∃ i, f p ∈ C i)
    (hcross : ∀ i j, i ≠ j → ∀ p ∈ K, f p ∈ C i → f p ∈ C j → p ∈ P)
    (hlocal : ∀ i p, p ∈ K \ P → f p ∈ C i →
      ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧ ∃ g : Base → ℝ,
        ContDiffOn ℝ ∞ g N ∧ (∀ x ∈ N, f x ∈ C i → g x = 0) ∧
          fderiv ℝ g p dy ≠ 0) :
    ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ g : Base → ℝ, ContDiffOn ℝ ∞ g N ∧ (∀ x ∈ K ∩ N, g x = 0) ∧
        fderiv ℝ g p dy ≠ 0 := by
  classical
  intro p hp
  obtain ⟨i,hi⟩ := hcover p hp.1
  obtain ⟨N,hN,hpN,g,hg,hzero,hderiv⟩ := hlocal i p hp hi
  have hav : ∀ᶠ x in 𝓝 p, ∀ j, j ≠ i → f x ∉ C j := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h => (h hji).elim)
    · have hj : f p ∉ C j := fun hj => hp.2 (hcross i j (Ne.symm hji) p hp.1 hi hj)
      filter_upwards [(hf p hp.1).eventually ((hC j).isOpen_compl.mem_nhds hj)] with x hx _
      exact hx
  obtain ⟨W,hWsub,hW,hpW⟩ := mem_nhds_iff.mp hav
  refine ⟨N ∩ W,hN.inter hW,⟨hpN,hpW⟩,g,hg.mono inter_subset_left,?_,hderiv⟩
  intro x hx
  obtain ⟨j,hj⟩ := hcover x hx.1
  have hji : j = i := by
    by_contra h
    exact hWsub hx.2.2 j h hj
  exact hzero x hx.2.1 (by simpa only [hji] using hj)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI

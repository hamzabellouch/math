import OAI.GroupTheory.PolycyclicRecognition.Geometry.LocalExponentialOpen

namespace OAI

/-! # Local coordinates from an invertible manifold differential

This is the chart reduction needed when the source of an integrated Lie
homomorphism is a manifold rather than a vector space.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold Topology ContDiff

variable {E F H M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ, F)) ∞ N]

theorem locally_injective_open_of_manifold_mfderiv_equiv
    {f : M → N} {x : M} (d : E ≃L[ℝ] F) (hIrange : Set.range I = univ)
    (hf : ContMDiffAt I (𝓘(ℝ, F)) ∞ f x)
    (hd : HasMFDerivAt I (𝓘(ℝ, F)) f x d.toContinuousLinearMap) :
    (∃ U ∈ 𝓝 x, InjOn f U) ∧ map f (𝓝 x) = 𝓝 (f x) := by
  let φ := extChartAt I x
  have hx : x ∈ φ.source := mem_extChartAt_source x
  have hleft : φ.symm (φ x) = x := φ.left_inv hx
  have hφ : ContMDiffAt (𝓘(ℝ, E)) I ∞ φ.symm (φ x) := by
    simpa only [hIrange, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x)
  have hφd : HasMFDerivAt (𝓘(ℝ, E)) I φ.symm (φ x)
      (ContinuousLinearMap.id ℝ E) := by
    apply (hφ.mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv
    have hh := mfderivWithin_range_extChartAt_symm (I := I) (x := x)
    rw [hIrange, mfderivWithin_univ] at hh
    exact hh
  have hq : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ (f ∘ φ.symm) (φ x) :=
    hf.comp_of_eq hφ hleft
  have hqd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) (f ∘ φ.symm) (φ x)
      d.toContinuousLinearMap := by
    have hd' : HasMFDerivAt I (𝓘(ℝ, F)) f (φ.symm (φ x))
        d.toContinuousLinearMap := by rwa [hleft]
    have hh : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) (f ∘ φ.symm) (φ x)
        (d.toContinuousLinearMap.comp (ContinuousLinearMap.id ℝ E)) :=
      hd'.comp (φ x) hφd
    apply hh.congr_mfderiv
    ext v
    rfl
  obtain ⟨⟨U, hU, hi⟩, hm⟩ := locally_injective_open_of_mfderiv_equiv d hq hqd
  constructor
  · refine ⟨φ.source ∩ φ ⁻¹' U, ?_, ?_⟩
    · exact inter_mem (extChartAt_source_mem_nhds (I := I) x)
        ((continuousAt_extChartAt x).preimage_mem_nhds hU)
    · intro a ha b hb hab
      apply φ.injOn ha.1 hb.1
      apply hi ha.2 hb.2
      simpa only [Function.comp_apply, φ.left_inv ha.1, φ.left_inv hb.1] using hab
  · have hψ : map φ.symm (𝓝 (φ x)) = 𝓝 x := by
      simpa only [φ, hIrange, nhdsWithin_univ] using
        map_extChartAt_symm_nhdsWithin_range (I := I) x
    calc
      map f (𝓝 x) = map f (map φ.symm (𝓝 (φ x))) := by rw [hψ]
      _ = map (f ∘ φ.symm) (𝓝 (φ x)) := map_map
      _ = 𝓝 (f (φ.symm (φ x))) := hm
      _ = 𝓝 (f x) := by rw [hleft]

end PolycyclicRecognition

end

end OAI

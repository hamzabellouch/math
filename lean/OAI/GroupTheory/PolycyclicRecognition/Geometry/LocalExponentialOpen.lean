import OAI.GroupTheory.PolycyclicRecognition.Geometry.DynkinLocalExponential

namespace OAI

/-! # Local injectivity and openness from an invertible manifold derivative -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold Topology ContDiff

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

theorem locally_injective_open_of_mfderiv_equiv
    {f : V → M} {x : V} (d : V ≃L[ℝ] E)
    (hf : ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) ∞ f x)
    (hd : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, E)) f x d.toContinuousLinearMap) :
    (∃ U ∈ 𝓝 x, InjOn f U) ∧ Filter.map f (𝓝 x) = 𝓝 (f x) := by
  let φ := extChartAt (𝓘(ℝ, E)) (f x)
  let Q := φ ∘ f
  have hφ : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ (f x) :=
    contMDiffAt_extChartAt
  have hQ : ContDiffAt ℝ ∞ Q x := (hφ.comp x hf).contDiffAt
  have hφd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (f x)
      (ContinuousLinearMap.id ℝ E) := by
    apply (hφ.mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv
    rw [mfderiv_extChartAt_self]
    rfl
  have hQd : HasFDerivAt Q d.toContinuousLinearMap x := by
    have hh : HasFDerivAt Q ((ContinuousLinearMap.id ℝ E).comp d.toContinuousLinearMap) x :=
      (hφd.comp x hd).hasFDerivAt
    simpa only [ContinuousLinearMap.id_comp] using hh
  have hstrict := hQ.hasStrictFDerivAt' hQd (by simp)
  let e := hstrict.toOpenPartialHomeomorph Q
  have hx : x ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  constructor
  · refine ⟨e.source, e.open_source.mem_nhds hx, ?_⟩
    intro a ha b hb hab
    apply e.injOn ha hb
    exact congrArg φ hab
  · have hQmap : Filter.map Q (𝓝 x) = 𝓝 (Q x) :=
      hstrict.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr d.surjective)
    have hsource : ∀ᶠ y in 𝓝 x, f y ∈ φ.source :=
      hf.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (f x))
    have hcomp : φ.symm ∘ Q =ᶠ[𝓝 x] f := hsource.mono fun y hy => φ.left_inv hy
    calc
      Filter.map f (𝓝 x) = Filter.map (φ.symm ∘ Q) (𝓝 x) := Filter.map_congr hcomp.symm
      _ = Filter.map φ.symm (Filter.map Q (𝓝 x)) := (Filter.map_map).symm
      _ = Filter.map φ.symm (𝓝 (Q x)) := by rw [hQmap]
      _ = 𝓝 (f x) := by
        simpa only [Q, φ, modelWithCornersSelf_coe, Set.range_id, nhdsWithin_univ,
          Function.comp_apply] using
          map_extChartAt_symm_nhdsWithin_range (I := 𝓘(ℝ, E)) (f x)

end PolycyclicRecognition

end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothImmersionCancellation

namespace OAI

/-! # The local chart form of smoothness cancellation -/

noncomputable section
namespace PolycyclicRecognition

open Filter Set
open scoped Manifold Topology ContDiff

variable {E V A N M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [TopologicalSpace N] [ChartedSpace E N]
  [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓘(ℝ, V)) ∞ M]

theorem contMDiffAt_of_comp_of_injective_mfderiv
    {f : N → M} {F : M → A} {x : N} {D : V →L[ℝ] A}
    (hf : ContinuousAt f x)
    (hF : ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, A)) ∞ F (f x))
    (hD : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, A)) F (f x) D)
    (hDi : Function.Injective D)
    (hcomp : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (F ∘ f) x) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ f x := by
  let φ := extChartAt (𝓘(ℝ, V)) (f x)
  have hinv : φ.symm (φ (f x)) = f x := φ.left_inv (mem_extChartAt_source (f x))
  have hφ : ContMDiffAt (𝓘(ℝ, V)) (𝓘(ℝ, V)) ∞ φ.symm (φ (f x)) := by
    simpa only [modelWithCornersSelf_coe, Set.range_id, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, V)) (n := ∞) (f x))
  have hφd : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, V)) φ.symm (φ (f x))
      (ContinuousLinearMap.id ℝ V) := by
    apply (hφ.mdifferentiableAt (by simp)).hasMFDerivAt.congr_mfderiv
    have hrange : Set.range (𝓘(ℝ, V)) = (Set.univ : Set V) := by ext v; simp
    have hh := mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ, V)) (x := f x)
    rw [hrange, mfderivWithin_univ] at hh
    exact hh
  have hF' : ContDiffAt ℝ ∞ (F ∘ φ.symm) (φ (f x)) :=
    (hF.comp_of_eq hφ hinv).contDiffAt
  have hD' : HasFDerivAt (F ∘ φ.symm) D (φ (f x)) := by
    have hd : HasMFDerivAt (𝓘(ℝ, V)) (𝓘(ℝ, A)) F (φ.symm (φ (f x))) D := by
      rwa [hinv]
    have hh : HasFDerivAt (F ∘ φ.symm) (D.comp (ContinuousLinearMap.id ℝ V))
        (φ (f x)) := (hd.comp _ hφd).hasFDerivAt
    simpa only [ContinuousLinearMap.comp_id] using hh
  have hc : ContinuousAt (φ ∘ f) x := (continuousAt_extChartAt (f x)).comp hf
  have heq : (F ∘ φ.symm) ∘ (φ ∘ f) =ᶠ[𝓝 x] F ∘ f := by
    filter_upwards [hf.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ, V)) (f x))]
      with y hy
    change F (φ.symm (φ (f y))) = F (f y)
    rw [φ.left_inv hy]
  apply contMDiffAt_iff_target.mpr
  refine ⟨hf, ?_⟩
  exact contMDiffAt_of_comp_of_injective_differential hc hF' hD' hDi
    (hcomp.congr_of_eventuallyEq heq)

end PolycyclicRecognition

end

end OAI

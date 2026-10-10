import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

namespace OAI

/-! # The local open mapping consequence needed for Cartan multiplication

This is a direct chartwise application of Mathlib's strict inverse function
theorem. It uses a surjective differential, without requiring complementary
Cartan factors or assuming a local product theorem.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter Set
open scoped Manifold Topology

variable {E E' H H' M M' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [TopologicalSpace M']
  [ChartedSpace H M] [ChartedSpace H' M']
  {f : M → M'} {x : M}

/-- A continuously differentiable map with surjective differential sends
the neighborhood filter exactly onto the neighborhood filter of its value. -/
theorem map_nhds_eq_of_surjective_mfderiv
    (hf : ContMDiffAt I J 1 f x)
    (hsurj : Function.Surjective (mfderiv I J f x)) :
    map f (𝓝 x) = 𝓝 (f x) := by
  let F := writtenInExtChartAt I J x f
  have hC : ContDiffAt ℝ 1 F (extChartAt I x x) := by
    simpa only [F, writtenInExtChartAt, I.range_eq_univ, contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp hf).2
  have hD := hf.mdifferentiableAt one_ne_zero
  have hF : Function.Surjective (fderiv ℝ F (extChartAt I x x)) := by
    intro y
    obtain ⟨v, hv⟩ := hsurj ((tangentSpaceCastModel J (f x)).symm y)
    refine ⟨tangentSpaceCastModel I x v, ?_⟩
    rw [hD.mfderiv] at hv
    simpa only [F, I.range_eq_univ, fderivWithin_univ, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.symm_apply_eq] using hv
  have hmap := (hC.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj
    (LinearMap.range_eq_top.mpr hF)
  have hvalue : F (extChartAt I x x) = extChartAt J (f x) (f x) := by
    simp only [F, writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]
  rw [hvalue] at hmap
  have hsource : map (extChartAt I x).symm (𝓝 (extChartAt I x x)) = 𝓝 x := by
    simpa only [I.range_eq_univ, nhdsWithin_univ] using
      (map_extChartAt_symm_nhdsWithin_range (I := I) x)
  have htarget : map (extChartAt J (f x)).symm
      (𝓝 (extChartAt J (f x) (f x))) = 𝓝 (f x) := by
    simpa only [J.range_eq_univ, nhdsWithin_univ] using
      (map_extChartAt_symm_nhdsWithin_range (I := J) (f x))
  have hcancel : (extChartAt J (f x)).symm ∘ extChartAt J (f x) ∘ f =ᶠ[𝓝 x] f := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds
      (extChartAt_source_mem_nhds (I := J) (f x))] with z hz
    exact (extChartAt J (f x)).left_inv hz
  calc
    map f (𝓝 x) = map ((extChartAt J (f x)).symm ∘ extChartAt J (f x) ∘ f) (𝓝 x) :=
      (Filter.map_congr hcancel).symm
    _ = map (extChartAt J (f x)).symm (map F (𝓝 (extChartAt I x x))) := by
      dsimp only [F, writtenInExtChartAt]
      simp only [← map_map]
      rw [hsource]
    _ = 𝓝 (f x) := by rw [hmap, htarget]

end PolycyclicRecognition

end

end OAI

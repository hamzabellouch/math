import Mathlib.Geometry.Manifold.Riemannian.Basic

namespace OAI

/-! # Chart displacement controlled by the length of a path -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory Manifold
open scoped Manifold ContDiff ENNReal NNReal Bundle

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) 1 M]
  [Bundle.RiemannianBundle (TangentSpace (𝓘(ℝ, E)) : M → Type _)]

local instance tangentModelOperatorENorm (x : M) (y : E) :
    ENorm (TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) y) :=
  inferInstanceAs (ENorm (TangentSpace (𝓘(ℝ, E)) x →L[ℝ] E))

theorem chart_edist_le_pathELength (x : M) (γ : ℝ → M)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 γ (Icc 0 1))
    (hsource : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (chartAt E x).source)
    (C : ℝ≥0) (hC : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x) (γ t)‖ₑ ≤ C) :
    edist (extChartAt (𝓘(ℝ, E)) x (γ 0)) (extChartAt (𝓘(ℝ, E)) x (γ 1)) ≤
      C * pathELength (𝓘(ℝ, E)) γ 0 1 := by
  let η := extChartAt (𝓘(ℝ, E)) x ∘ γ
  have hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 η (Icc 0 1) :=
    contMDiffOn_extChartAt.comp hγ hsource
  calc
    _ = ‖η 1 - η 0‖ₑ := by rw [edist_comm, edist_eq_enorm_sub]; rfl
    _ ≤ ∫⁻ t in Icc 0 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη.contDiffOn zero_le_one
    _ = ∫⁻ t in Icc 0 1, ‖mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) η (Icc 0 1) t 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t in Icc 0 1, C * ‖mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (Icc 0 1) t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hd : mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) η (Icc 0 1) t =
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x) (γ t)).comp
            (mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (Icc 0 1) t) := by
        apply mfderiv_comp_mfderivWithin
        · exact mdifferentiableAt_extChartAt (hsource t ht)
        · exact (hγ.mdifferentiableOn one_ne_zero) t ht
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one t ht
      have hv := congrArg (fun D => D (1 : TangentSpace (𝓘(ℝ, ℝ)) t)) hd
      rw [hv]
      change ‖mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) x) (γ t)
        (mfderivWithin (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) γ (Icc 0 1) t 1)‖ₑ ≤ _
      apply (ContinuousLinearMap.le_opENorm _ _).trans
      gcongr
      exact hC t ht
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        pathELength_eq_lintegral_mfderivWithin_Icc]

end PolycyclicRecognition

end

end OAI

import Mathlib
import OAI.Analysis.BiholderTransport.Model
import OAI.Analysis.BiholderTransport.Calculus.RiemannianContinuous

namespace OAI

section
section
noncomputable section
open Set Filter Manifold MeasureTheory Bundle Metric
open scoped Topology ContDiff ENNReal NNReal

namespace WeakMTWTransport
section ChartLipschitz
variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

local instance (y : Model n) (x : M) : NormedAddCommGroup
    (TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance (y : Model n) (x : M) : NormedSpace ℝ
    (TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x) :=
  ContinuousLinearMap.toNormedSpace

lemma exists_lipschitz_inverse_chart (x : M) :
    ∃ C : ℝ≥0, ∃ r>0, ball (extChartAt 𝓘(ℝ,Model n) x x) r ⊆ (extChartAt 𝓘(ℝ,Model n) x).target ∧
      LipschitzOnWith C (extChartAt 𝓘(ℝ,Model n) x).symm
        (ball (extChartAt 𝓘(ℝ,Model n) x x) r) := by
  let d := extChartAt 𝓘(ℝ,Model n) x
  have : IsContinuousRiemannianBundle (Model n) (fun z : M => TangentSpace 𝓘(ℝ,Model n) z) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  obtain ⟨C,hCpos,hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt 𝓘(ℝ,Model n) x
  have hC' : ∀ᶠ y in 𝓝 (d x), ‖mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm y‖ₑ < C := by
    simpa only [ModelWithCorners.range_eq_univ,nhdsWithin_univ,mfderivWithin_univ] using hC
  have hdT : d.target∈𝓝 (d x) :=
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  obtain ⟨r,hr,hboth⟩ := Metric.mem_nhds_iff.mp (inter_mem hdT hC')
  have htarget : ball (d x) r⊆d.target := fun y hy => (hboth hy).1
  have hbound : ∀ y∈ball (d x) r, ‖mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm y‖ₑ≤C :=
    fun y hy => (hboth hy).2.le
  refine ⟨C,r,hr,htarget,?_⟩
  intro u hu v hv
  let η := ContinuousAffineMap.lineMap (R := ℝ) u v
  let γ := d.symm ∘ η
  have hη : MapsTo η (Icc 0 1) (ball (d x) r) := by
    change Icc 0 1 ⊆ η ⁻¹' ball (d x) r
    rw [←image_subset_iff]
    simp only [η,ContinuousAffineMap.coe_lineMap_eq,←segment_eq_image_lineMap]
    exact (convex_ball _ _).segment_subset hu hv
  have hηT : MapsTo η (Icc 0 1) d.target := hη.mono_right htarget
  have η_smooth : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) 1 η (Icc 0 1) :=
    (ContinuousAffineMap.contDiff η).contMDiff.contMDiffOn
  have hγ : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) 1 γ (Icc 0 1) :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,Model n)) (n := (1:ℕ∞ω)) x).comp η_smooth hηT
  have H : riemannianEDist 𝓘(ℝ,Model n) (d.symm u) (d.symm v)≤pathELength 𝓘(ℝ,Model n) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact hγ
    · simp only [γ,Function.comp_apply,η,ContinuousAffineMap.coe_lineMap_eq,AffineMap.lineMap_apply_zero]
    · simp only [γ,Function.comp_apply,η,ContinuousAffineMap.coe_lineMap_eq,AffineMap.lineMap_apply_one]
  rw [←IsRiemannianManifold.out] at H
  apply H.trans
  rw [←lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ←lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hD : mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) γ (Icc 0 1) t =
      (mfderiv 𝓘(ℝ,Model n) 𝓘(ℝ,Model n) d.symm (η t)).comp (mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,Model n) η (Icc 0 1) t) := by
    apply mfderiv_comp_mfderivWithin
    · exact (contMDiffWithinAt_extChartAt_symm_target (n := (1:ℕ∞ω)) x (hηT ht)).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (hηT ht)) |>.mdifferentiableAt (by norm_num : (1:ℕ∞ω)≠0)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  rw [hD,ContinuousLinearMap.comp_apply]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact hbound _ (hη ht)
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_rfl

end ChartLipschitz
end WeakMTWTransport

end

end

end

end OAI

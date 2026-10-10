import Mathlib
import OAI.Geometry.TamingCompatibility.Model
import OAI.Geometry.TamingCompatibility.Functional.ContinuousBundleNorm

namespace OAI


noncomputable section
namespace TamingCompatibility
open Bundle Manifold Set MeasureTheory Filter
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [RiemannianBundle (TangentSpace Model : X → Type)]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

lemma smooth_mfderiv_uniform_bound {f : X → Space} (hf : ContMDiff Model Model ∞ f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : X) (v : TangentSpace Model x),
      ‖mfderiv Model Model f x v‖ ≤ C*‖v‖ := by
  have hc : Continuous (fun p : TangentBundle Model X =>
      ‖mfderiv Model Model f p.proj p.2‖) :=
    (((contMDiff_snd_tangentBundle_modelSpace (n := ∞) Space Model).continuous.comp
      (hf.continuous_tangentMap (by simp))).norm)
  obtain ⟨C,hC⟩ := (isCompact_bundle_unitSphere (E := TangentSpace Model)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x v
  by_cases hv : v = 0
  · simp [hv]
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by simp [norm_smul,hnv.ne']
  have hb := hC ⟨x,(‖v‖⁻¹ : ℝ) • v⟩ hu
  simp only [ContinuousLinearMap.map_smul,norm_smul,Real.norm_eq_abs,
    abs_inv,abs_of_pos hnv] at hb
  have hb' := (le_abs_self _).trans hb
  have h : ‖mfderiv Model Model f x v‖ ≤ C*‖v‖ := by
    apply (div_le_iff₀ hnv).mp
    simpa only [div_eq_mul_inv,mul_comm] using hb'
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v))

omit [IsManifold Model ∞ X] [T2Space X] [CompactSpace X]
  [IsContinuousRiemannianBundle Space (TangentSpace Model : X → Type)] in

lemma smooth_edist_le_length {f : X → Space} (hf : ContMDiff Model Model ∞ f)
    {C : ℝ≥0} (hC : ∀ (x : X) (v : TangentSpace Model x),
      ‖mfderiv Model Model f x v‖ ≤ C*‖v‖)
    {γ : ℝ → X} (hγ : ContMDiff 𝓘(ℝ,ℝ) Model 1 γ) :
    edist (f (γ 1)) (f (γ 0)) ≤ C * pathELength Model γ 0 1 := by
  let η := f ∘ γ
  have hη : ContDiff ℝ 1 η := contMDiff_iff_contDiff.mp ((hf.of_le (by simp)).comp hγ)
  calc
    _ = ‖η 1 - η 0‖ₑ := edist_eq_enorm_sub _ _
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη.contDiffOn zero_le_one
    _ = ∫⁻ t in Icc (0:ℝ) 1, ‖mfderiv 𝓘(ℝ,ℝ) Model η t 1‖ₑ := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      simp only
      rw [← fderivWithin_derivWithin,
        (hη.differentiable (by simp) t).fderivWithin (uniqueDiffOn_Icc zero_lt_one t ht),
        mfderiv_eq_fderiv]
      rfl
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, (C:ℝ≥0∞)*‖mfderiv 𝓘(ℝ,ℝ) Model γ t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t _ht
      have he := mfderiv_comp t (hf.mdifferentiable (by simp) (γ t))
        (hγ.mdifferentiable (by simp) t)
      change ‖mfderiv 𝓘(ℝ,ℝ) Model (f ∘ γ) t 1‖ₑ ≤ _
      rw [he,ContinuousLinearMap.comp_apply]
      have h := ENNReal.ofReal_le_ofReal (hC (γ t) (mfderiv 𝓘(ℝ,ℝ) Model γ t 1))
      simpa only [← ofReal_norm,ENNReal.ofReal_mul C.coe_nonneg,ENNReal.ofReal_coe_nnreal] using h
    _ = C * pathELength Model γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,pathELength]

theorem smooth_lipschitz_riemannian {f : X → Space} (hf : ContMDiff Model Model ∞ f) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x y : X,
      edist (f x) (f y) ≤ C * riemannianEDist Model x y := by
  obtain ⟨C,hCp,hC⟩ := smooth_mfderiv_uniform_bound hf
  lift C to ℝ≥0 using hCp.le
  refine ⟨C,hCp,?_⟩
  intro x y
  have hCnp : (C:ℝ≥0∞) ≠ 0 := by exact_mod_cast hCp.ne'
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hεfin
  by_cases hd : riemannianEDist Model x y = ⊤
  · simp [hd,hCnp]
  have hd' : riemannianEDist Model x y < riemannianEDist Model x y + ε/(C:ℝ≥0∞) := by
    exact ENNReal.lt_add_right hd (ENNReal.div_ne_zero.mpr ⟨by exact_mod_cast hε.ne', ENNReal.coe_ne_top⟩)
  obtain ⟨γ,hγx,hγy,hγ,hγlen,_⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hd' zero_lt_one
  have hh := smooth_edist_le_length hf hC hγ
  rw [hγx,hγy,edist_comm] at hh
  calc
    _ ≤ C * pathELength Model γ 0 1 := hh
    _ ≤ C * (riemannianEDist Model x y + ε/(C:ℝ≥0∞)) := by gcongr
    _ = C*riemannianEDist Model x y + ε := by
      rw [mul_add,ENNReal.mul_div_cancel (by exact_mod_cast hCp.ne') ENNReal.coe_ne_top]
end TamingCompatibility

end

end OAI

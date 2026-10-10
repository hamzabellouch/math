import Mathlib

namespace OAI

/-! Smooth superposition on continuous paths and Volterra integration. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.SmoothFlow
open Set Filter ContinuousLinearMap
open scoped ContDiff Topology
universe u v
variable {K : Type v} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def pointwiseLinear (A : C(K,E →L[ℝ] F)) : C(K,E) →L[ℝ] C(K,F) := by
  let L : C(K,E) →ₗ[ℝ] C(K,F) :=
    { toFun := fun v => ⟨fun k => A k (v k), A.continuous.clm_apply v.continuous⟩
      map_add' := by intro u v; ext k; exact (A k).map_add _ _
      map_smul' := by intro c v; ext k; exact (A k).map_smul c _ }
  exact L.mkContinuous ‖A‖ (fun v => by
    apply (ContinuousMap.norm_le (L v) (mul_nonneg (norm_nonneg A) (norm_nonneg v))).mpr
    intro k
    exact ((A k).le_opNorm (v k)).trans
      (mul_le_mul (ContinuousMap.norm_coe_le_norm A k)
        (ContinuousMap.norm_coe_le_norm v k) (norm_nonneg _) (norm_nonneg _)))

@[simp] lemma pointwiseLinear_apply (A : C(K,E →L[ℝ] F)) (v : C(K,E)) (k : K) :
    pointwiseLinear A v k = A k (v k) := rfl

def pointwiseOperator : C(K,E →L[ℝ] F) →L[ℝ] (C(K,E) →L[ℝ] C(K,F)) := by
  let L : C(K,E →L[ℝ] F) →ₗ[ℝ] (C(K,E) →L[ℝ] C(K,F)) :=
    { toFun := pointwiseLinear
      map_add' := by intro A B; ext v k; rfl
      map_smul' := by intro c A; ext v k; rfl }
  exact L.mkContinuous 1 (fun (A : C(K,E →L[ℝ] F)) => by
    rw [one_mul]
    change ‖pointwiseLinear A‖ ≤ ‖A‖
    exact (pointwiseLinear A).opNorm_le_bound (norm_nonneg A) (fun v =>
      (ContinuousMap.norm_le (pointwiseLinear A v)
        (mul_nonneg (norm_nonneg A) (norm_nonneg v))).mpr
        (fun k => ((A k).le_opNorm (v k)).trans
          (mul_le_mul (ContinuousMap.norm_coe_le_norm A k)
            (ContinuousMap.norm_coe_le_norm v k) (norm_nonneg _) (norm_nonneg _)))))

@[simp] lemma pointwiseOperator_apply (A : C(K,E →L[ℝ] F)) :
    pointwiseOperator A = pointwiseLinear A := rfl

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in

lemma uniform_zero_radius {G : K × E → F} (hG : Continuous G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ k v, ‖v‖ ≤ r → ‖G (k,v)-G (k,0)‖ < ε := by
  have he : ∀ᶠ v : E in 𝓝 0, ∀ k : K, ‖G (k,v)-G (k,0)‖ < ε := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (x₀:=(0:E)) (P:=fun v k => ‖G (k,v)-G (k,0)‖ < ε) (fun k _ => by
        have hc : Continuous (fun z : E × K => ‖G (z.2,z.1)-G (z.2,0)‖) :=
          ((hG.comp (continuous_snd.prodMk continuous_fst)).sub
            (hG.comp (continuous_snd.prodMk continuous_const))).norm
        exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hε))
    simpa only [mem_univ,forall_true_left] using h
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r/2,half_pos hr,fun k v hv => hball ?_ k⟩
  simpa only [Metric.mem_ball,dist_zero_right] using hv.trans_lt (half_lt_self hr)

theorem hasFDerivAt_superposition {f : E → F}
    (hf : Differentiable ℝ f) (hdf : Continuous (fderiv ℝ f)) (g : C(K,E)) :
    HasFDerivAt (fun v : C(K,E) => (⟨f,hf.continuous⟩ : C(E,F)).comp v)
      (pointwiseLinear ((⟨fderiv ℝ f,hdf⟩ : C(E,E →L[ℝ] F)).comp g)) g := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have hc : Continuous (fun z : K × E => fderiv ℝ f (g z.1+z.2)) :=
    hdf.comp ((g.continuous.comp continuous_fst).add continuous_snd)
  obtain ⟨r,hr,hvar⟩ := uniform_zero_radius hc hε
  filter_upwards [Metric.ball_mem_nhds (0:C(K,E)) hr] with v hv
  have hvn : ‖v‖ < r := by simpa using hv
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro k
  let A := fderiv ℝ f (g k)
  let R : E → F := fun w => f (g k+w)-A w
  have hdR : ∀ w, HasFDerivAt R (fderiv ℝ f (g k+w)-A) w := by
    intro w
    have ht := (hf (g k+w)).hasFDerivAt.comp w
      ((hasFDerivAt_const (g k) w).add (hasFDerivAt_id w))
    simpa only [R,Function.comp_def,zero_add,comp_id,Pi.sub_def] using ht.sub A.hasFDerivAt
  have he := (convex_closedBall (0:E) r).norm_image_sub_le_of_norm_fderiv_le
    (f:=R) (x:=(0:E)) (y:=v k)
    (fun w _ => (hdR w).differentiableAt)
    (fun w hw => by
      rw [(hdR w).fderiv]
      simpa only [A,add_zero] using (hvar k w (by simpa using hw)).le)
    (by simpa using hr.le) (show v k ∈ Metric.closedBall (0:E) r from by
      simpa using (ContinuousMap.norm_coe_le_norm v k).trans hvn.le)
  have he' : ‖f (g k+v k)-f (g k)-A (v k)‖ ≤ ε*‖v k‖ := by
    have heq : R (v k)-R 0 = f (g k+v k)-f (g k)-A (v k) := by
      dsimp only [R]
      simp only [map_zero,sub_zero,add_zero]
      abel
    simpa only [heq,sub_zero] using he
  change ‖f (g k+v k)-f (g k)-A (v k)‖ ≤ ε*‖v‖
  exact he'.trans (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm v k) hε.le)

theorem contDiff_superposition_nat (n : ℕ) {f : E → F} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun v : C(K,E) => (⟨f,hf.continuous⟩ : C(E,F)).comp v) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (ContinuousMap.continuous_postcomp _)
  | succ n ih =>
    have hd : Differentiable ℝ f := hf.differentiable (by simp)
    have hdf : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by simp)
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun v => pointwiseOperator (((⟨fderiv ℝ f,hdf.continuous⟩ :
      C(E,E →L[ℝ] F)).comp v)), ?_, ?_⟩
    · exact (pointwiseOperator (K:=K) (E:=E) (F:=F)).contDiff.comp (ih hdf)
    · intro x
      simpa only [pointwiseOperator_apply] using
        hasFDerivAt_superposition (K:=K) hd hdf.continuous x

theorem contDiff_superposition {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun v : C(K,E) => (⟨f,hf.continuous⟩ : C(E,F)).comp v) := by
  apply contDiff_infty.mpr
  intro n
  exact contDiff_superposition_nat n (contDiff_infty.mp hf n)

end NearbyLagrangian.SmoothFlow

namespace NearbyLagrangian.SmoothFlow
open Set Filter ContinuousLinearMap MeasureTheory
open scoped ContDiff Topology
abbrev UnitTime := Icc (0:ℝ) 1
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def pathExtend (v : C(UnitTime,E)) : ℝ → E := IccExtend zero_le_one v

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma continuous_pathExtend (v : C(UnitTime,E)) : Continuous (pathExtend v) :=
  v.continuous.Icc_extend'

omit [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] lemma pathExtend_coe (v : C(UnitTime,E)) (s : UnitTime) :
    pathExtend v s = v s := IccExtend_val _ _ _

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma norm_pathExtend_le (v : C(UnitTime,E)) (s : ℝ) : ‖pathExtend v s‖ ≤ ‖v‖ :=
  ContinuousMap.norm_coe_le_norm v _

def volterra : C(UnitTime,E) →L[ℝ] C(UnitTime,E) := by
  let L : C(UnitTime,E) →ₗ[ℝ] C(UnitTime,E) :=
    { toFun := fun v => ⟨fun s => ∫ t in (0:ℝ)..(s:ℝ), pathExtend v t,
        (intervalIntegral.differentiable_integral_of_continuous
          (continuous_pathExtend v)).continuous.comp continuous_subtype_val⟩
      map_add' := by
        intro v w
        ext s
        change (∫ t in (0:ℝ)..(s:ℝ), pathExtend v t+pathExtend w t) = _
        exact intervalIntegral.integral_add
          ((continuous_pathExtend v).intervalIntegrable _ _)
          ((continuous_pathExtend w).intervalIntegrable _ _)
      map_smul' := by
        intro c v
        ext s
        change (∫ t in (0:ℝ)..(s:ℝ), c • pathExtend v t) = _
        exact intervalIntegral.integral_smul c _ }
  exact L.mkContinuous 1 (fun (v : C(UnitTime,E)) => by
    rw [one_mul]
    apply (ContinuousMap.norm_le (L v) (norm_nonneg v)).mpr
    intro s
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(0:ℝ)) (b:=(s:ℝ)) (f:=pathExtend v) (C:=‖v‖)
      (fun t _ => norm_pathExtend_le v t)
    change ‖∫ t in (0:ℝ)..(s:ℝ), pathExtend v t‖ ≤ ‖v‖
    exact he.trans (by
      rw [sub_zero,abs_of_nonneg s.property.1]
      exact mul_le_of_le_one_right (norm_nonneg v) s.property.2))

@[simp] lemma volterra_apply (v : C(UnitTime,E)) (s : UnitTime) :
    volterra v s = ∫ t in (0:ℝ)..(s:ℝ), pathExtend v t := rfl

lemma norm_volterra_le : ‖(volterra : C(UnitTime,E) →L[ℝ] C(UnitTime,E))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg v)).mpr
  intro s
  rw [volterra_apply]
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=(s:ℝ)) (f:=pathExtend v) (C:=‖v‖)
    (fun t _ => norm_pathExtend_le v t)
  exact he.trans (by
    rw [sub_zero,abs_of_nonneg s.property.1]
    exact mul_le_of_le_one_right (norm_nonneg v) s.property.2)

end NearbyLagrangian.SmoothFlow

end

end OAI

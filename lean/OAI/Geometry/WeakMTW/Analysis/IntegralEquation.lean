import Mathlib
import OAI.Geometry.WeakMTW.Analysis.CurveComposition

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
namespace SmoothODE

open Set Filter
open scoped Topology ContDiff unitInterval
noncomputable section

universe v
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

def integralOperator : C(I, E) →L[ℝ] C(I, E) :=
  LinearMap.mkContinuous
    { toFun := fun u =>
        ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), u (projIcc 0 1 zero_le_one s),
          (intervalIntegral.continuous_primitive
            (fun a b => (u.continuous.comp continuous_projIcc).intervalIntegrable a b) 0).comp
            continuous_subtype_val⟩
      map_add' := by
        intro u v; ext t
        exact intervalIntegral.integral_add
          ((u.continuous.comp continuous_projIcc).intervalIntegrable _ _)
          ((v.continuous.comp continuous_projIcc).intervalIntegrable _ _)
      map_smul' := by
        intro a u; ext t
        exact intervalIntegral.integral_smul a _ }
    1 (by
      intro u
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg u)).2
      intro t
      calc
        ‖∫ s in (0 : ℝ)..(t : ℝ), u (projIcc 0 1 zero_le_one s)‖ ≤ ‖u‖ * |(t : ℝ) - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => u.norm_coe_le_norm _)
        _ ≤ ‖u‖ * 1 := by
          gcongr
          simpa only [sub_zero, abs_of_nonneg t.2.1] using t.2.2
        _ = ‖u‖ := mul_one _)

@[simp] theorem integralOperator_apply (u : C(I, E)) (t : I) :
    integralOperator u t = ∫ s in (0 : ℝ)..(t : ℝ), u (projIcc 0 1 zero_le_one s) := rfl

@[simp] theorem integralOperator_zero (u : C(I, E)) : integralOperator u 0 = 0 := by
  simp

section Inverse
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace E]

theorem exists_smooth_local_inverse {f : E → F} (hf : ContDiff ℝ ∞ f)
    {a : E} {e : E ≃L[ℝ] F} (he : HasFDerivAt f (e : E →L[ℝ] F) a) :
    ∃ (g : F → E) (V : Set F), IsOpen V ∧ f a ∈ V ∧
      g (f a) = a ∧ ContDiffOn ℝ ∞ g V ∧ ∀ y ∈ V, f (g y) = y := by
  let P := hf.contDiffAt.toOpenPartialHomeomorph f he (by simp)
  have hP : (P : E → F) = f := rfl
  have ha : a ∈ P.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source he (by simp)
  let U : Set E := (fderiv ℝ f) ⁻¹' Set.range ((↑) : (E ≃L[ℝ] F) → E →L[ℝ] F)
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen.preimage (hf.continuous_fderiv (by simp))
  have haU : a ∈ U := ⟨e, he.fderiv.symm⟩
  let V := P.target ∩ P.symm ⁻¹' U
  have hV : IsOpen V := P.isOpen_inter_preimage_symm hU
  have hfa : f a ∈ V := by
    refine ⟨P.map_source ha, ?_⟩
    change P.symm (f a) ∈ U
    rw [← hP, P.left_inv ha]
    exact haU
  refine ⟨P.symm, V, hV, hfa, ?_, ?_, ?_⟩
  · exact P.left_inv ha
  · intro y hy
    obtain ⟨e', he'⟩ := hy.2
    apply ContDiffAt.contDiffWithinAt
    apply P.contDiffAt_symm hy.1 (f₀' := e')
    · rw [hP, he']
      exact (hf.differentiable (by simp) _).hasFDerivAt
    · rw [hP]
      exact hf.contDiffAt
  · intro y hy
    exact P.right_inv hy.1

end Inverse

def subtractShear (b : E) : (ℝ × E) ≃L[ℝ] (ℝ × E) where
  toFun z := (z.1, z.2 - z.1 • b)
  invFun z := (z.1, z.2 + z.1 • b)
  map_add' := by
    intro z w; ext <;> simp [add_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  map_smul' := by
    intro c z; ext <;> simp [smul_sub, mul_smul]
  left_inv := by intro z; ext <;> simp
  right_inv := by intro z; ext <;> simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.sub (continuous_fst.smul continuous_const))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.add (continuous_fst.smul continuous_const))

@[simp] theorem subtractShear_apply (b : E) (z : ℝ × E) :
    subtractShear b z = (z.1, z.2 - z.1 • b) := rfl

variable [FiniteDimensional ℝ E]

theorem exists_smooth_integral_curves {f : E → E} (hf : ContDiff ℝ ∞ f) (x₀ : E) :
    ∃ (U : Set (ℝ × E)) (Ψ : ℝ × E → C(I, E)),
      IsOpen U ∧ (0, x₀) ∈ U ∧ ContDiffOn ℝ ∞ Ψ U ∧
      Ψ (0, x₀) = ContinuousMap.const I x₀ ∧
      ∀ q ∈ U, Ψ q = ContinuousMap.const I q.2 +
        q.1 • integralOperator (ContinuousMap.comp ⟨f, hf.continuous⟩ (Ψ q)) := by
  let B : C(I, E) → C(I, E) := fun u =>
    integralOperator (ContinuousMap.comp ⟨f, hf.continuous⟩ u)
  have hB : ContDiff ℝ ∞ B :=
    integralOperator.contDiff.comp (SmoothCurveComposition.contDiff_postcomp hf)
  let H : ℝ × C(I, E) → ℝ × C(I, E) := fun z => (z.1, z.2 - z.1 • B z.2)
  have hH : ContDiff ℝ ∞ H :=
    contDiff_fst.prodMk (contDiff_snd.sub (contDiff_fst.smul (hB.comp contDiff_snd)))
  let u₀ : C(I, E) := ContinuousMap.const I x₀
  have hHd : HasFDerivAt H (subtractShear (B u₀) : (ℝ × C(I, E)) →L[ℝ] (ℝ × C(I, E)))
      (0, u₀) := by
    have hdB : HasFDerivAt (fun z : ℝ × C(I, E) => B z.2)
        ((fderiv ℝ B u₀).comp (ContinuousLinearMap.snd ℝ ℝ C(I, E))) (0, u₀) :=
      HasFDerivAt.comp (f := Prod.snd) (g := B) (0, u₀)
        (hB.differentiable (by simp) u₀).hasFDerivAt hasFDerivAt_snd
    have hd := hasFDerivAt_fst.prodMk (hasFDerivAt_snd.sub
      (hasFDerivAt_fst.smul hdB))
    convert! hd using 1
    ext z <;> simp [subtractShear]
  obtain ⟨g, V, hVo, hVmem, hg0, hg, hgr⟩ := exists_smooth_local_inverse hH hHd
  have hH0 : H (0, u₀) = (0, u₀) := by simp [H]
  rw [hH0] at hVmem hg0
  let J : ℝ × E → ℝ × C(I, E) := fun q => (q.1, ContinuousMap.const I q.2)
  have hJ : ContDiff ℝ ∞ J :=
    contDiff_fst.prodMk ((ContinuousLinearMap.const ℝ I : E →L[ℝ] C(I, E)).contDiff.comp contDiff_snd)
  refine ⟨J ⁻¹' V, fun q => (g (J q)).2, hVo.preimage hJ.continuous, hVmem, ?_, ?_, ?_⟩
  · exact (hg.comp hJ.contDiffOn (fun q hq => hq)).snd
  · exact congrArg Prod.snd hg0
  · intro q hq
    have he := hgr (J q) hq
    have he1 : (g (J q)).1 = q.1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change (g (J q)).2 - (g (J q)).1 • B (g (J q)).2 = ContinuousMap.const I q.2 at he2
    rw [he1] at he2
    exact sub_eq_iff_eq_add.mp he2

omit [FiniteDimensional ℝ E] in
theorem integral_curve_initial {f : C(E, E)} {q : ℝ × E} {u : C(I, E)}
    (hu : u = ContinuousMap.const I q.2 + q.1 • integralOperator (f.comp u)) :
    u 0 = q.2 := by
  have h := congrArg (fun v : C(I, E) => v 0) hu
  simpa using h

theorem integral_curve_derivative {f : C(E, E)} {q : ℝ × E} {u : C(I, E)}
    (hu : u = ContinuousMap.const I q.2 + q.1 • integralOperator (f.comp u))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => u (projIcc 0 1 zero_le_one s))
      (q.1 • f (u ⟨t, ht⟩)) (Icc (0 : ℝ) 1) t := by
  let v : ℝ → E := fun s => f (u (projIcc 0 1 zero_le_one s))
  have hv : Continuous v := f.continuous.comp (u.continuous.comp continuous_projIcc)
  have hd := ((intervalIntegral.integral_hasDerivAt_right
    (hv.intervalIntegrable 0 t) (hv.stronglyMeasurableAtFilter _ _) hv.continuousAt).const_smul q.1).const_add q.2
  have heq : ∀ s ∈ Icc (0 : ℝ) 1, u (projIcc 0 1 zero_le_one s) =
      q.2 + q.1 • ∫ r in (0 : ℝ)..s, v r := by
    intro s hs
    have h := congrArg (fun w : C(I, E) => w ⟨s, hs⟩) hu
    simpa only [ContinuousMap.add_apply, ContinuousMap.const_apply,
      ContinuousMap.smul_apply, integralOperator_apply, ContinuousMap.comp_apply,
      projIcc_of_mem zero_le_one hs] using h
  have hd' := hd.hasDerivWithinAt.congr_of_mem heq ht
  simpa only [v, projIcc_of_mem zero_le_one ht] using hd'

theorem exists_smooth_extension {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {S : Set E} (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S)
    {a : E} (ha : a ∈ S) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 a] f := by
  obtain ⟨d, hd, hds⟩ := Euclidean.nhds_basis_closedBall.mem_iff.mp (hS.mem_nhds ha)
  let b : ContDiffBump (toEuclidean a) :=
    { rIn := d / 2, rOut := d, rIn_pos := half_pos hd,
      rIn_lt_rOut := half_lt_self hd }
  let β : E → ℝ := b ∘ toEuclidean
  have hβ : ContDiff ℝ ∞ β := b.contDiff.comp (ContinuousLinearEquiv.contDiff _)
  have hsupp : tsupport β ⊆ S := by
    apply subset_trans _ hds
    rw [tsupport, ← Euclidean.closure_ball _ hd.ne']
    apply closure_mono
    intro y hy
    have hby : toEuclidean y ∈ Function.support b := hy
    rwa [b.support_eq] at hby
  have heq : β =ᶠ[𝓝 a] 1 :=
    b.eventuallyEq_one.comp_tendsto (toEuclidean.continuous.tendsto a)
  refine ⟨fun x => β x • f x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport β
    · exact hβ.contDiffAt.smul ((hf x (hsupp hx)).contDiffAt (hS.mem_nhds (hsupp hx)))
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
      simp only [hy, Pi.zero_apply, zero_smul]
  · filter_upwards [heq] with x hx
    simp only [hx, Pi.one_apply, one_smul]

theorem exists_smooth_local_curves {f : E → E} {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) {x₀ : E} (hx₀ : x₀ ∈ S) :
    ∃ (U : Set (ℝ × E)) (Ψ : ℝ × E → C(I, E)),
      IsOpen U ∧ (0, x₀) ∈ U ∧ ContDiffOn ℝ ∞ Ψ U ∧
      Ψ (0, x₀) = ContinuousMap.const I x₀ ∧
      ∀ q ∈ U, Ψ q 0 = q.2 ∧ (∀ s : I, Ψ q s ∈ S) ∧
        ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
          HasDerivWithinAt (fun s => Ψ q (projIcc 0 1 zero_le_one s))
            (q.1 • f (Ψ q ⟨t, ht⟩)) (Icc (0 : ℝ) 1) t := by
  obtain ⟨g, hg, hgf⟩ := exists_smooth_extension hS hf hx₀
  obtain ⟨r, hr, hrg⟩ := Metric.eventually_nhds_iff.mp
    (hgf.and (hS.mem_nhds hx₀))
  obtain ⟨U, Ψ, hU, hmem, hΨ, hΨ₀, hsol⟩ := exists_smooth_integral_curves hg x₀
  let W := U ∩ Ψ ⁻¹' Metric.ball (ContinuousMap.const I x₀) r
  have hW : IsOpen W := hΨ.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hWmem : (0, x₀) ∈ W := ⟨hmem, by simpa [hΨ₀] using hr⟩
  refine ⟨W, Ψ, hW, hWmem, hΨ.mono inter_subset_left, hΨ₀, ?_⟩
  intro q hq
  have hnear : ∀ t : I, dist (Ψ q t) x₀ < r := by
    intro t
    have hn := (Ψ q - ContinuousMap.const I x₀).norm_coe_le_norm t
    have hb := hq.2
    rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hb
    simpa only [ContinuousMap.sub_apply, ContinuousMap.const_apply, dist_eq_norm] using hn.trans_lt hb
  have hgeq : ∀ t : I, g (Ψ q t) = f (Ψ q t) := fun t => (hrg (hnear t)).1
  refine ⟨integral_curve_initial (hsol q hq.1), fun t => (hrg (hnear t)).2, ?_⟩
  intro t ht
  have hd := integral_curve_derivative (hsol q hq.1) ht
  simpa only [ContinuousMap.coe_mk, hgeq] using hd

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_endpoint {U : Set (ℝ × E)} {Ψ : ℝ × E → C(I, E)}
    (hΨ : ContDiffOn ℝ ∞ Ψ U) : ContDiffOn ℝ ∞ (fun q => Ψ q 1) U :=
  (ContinuousMap.evalCLM ℝ (1 : I) : C(I, E) →L[ℝ] E).contDiff.comp_contDiffOn hΨ

end
end SmoothODE

end

end WeakMTWGlobalSupport

end OAI

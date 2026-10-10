import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetLinear
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatDataEquation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.TangentCone.Real

namespace OAI

/-! Smooth time curves of compatible spatial jets are jointly smooth on the closed slab. -/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets
open ShearFlows Set Filter
open scoped Topology ContDiff BigOperators BoundedContinuousFunction

structure SmoothPlaneCurves (T : ℝ) where
  curve : ∀ k, ℝ → Space Plane ℝ k
  smooth : ∀ k, ContDiffOn ℝ ∞ (curve k) (Icc 0 T)
  compatible : ∀ k n (hkn : k ≤ n) t, t ∈ Icc (0 : ℝ) T →
    truncateCLM Plane ℝ k n hkn (curve n t) = curve k t

namespace SmoothPlaneCurves

def value {T : ℝ} (J : SmoothPlaneCurves T) (p : ℝ × Plane) : ℝ :=
  function Plane ℝ 0 (J.curve 0 p.1) p.2

theorem value_eq {T : ℝ} (J : SmoothPlaneCurves T) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (fun x => J.value (t,x)) = (function Plane ℝ k (J.curve k t) : Plane → ℝ) := by
  funext x
  have he := congrArg (fun L : Space Plane ℝ 0 => function Plane ℝ 0 L x)
    (J.compatible 0 k (Nat.zero_le k) t ht)
  change function Plane ℝ 0 (truncate Plane ℝ 0 k (Nat.zero_le k) (J.curve k t)) x = _ at he
  rw [function_truncate] at he
  exact he.symm

theorem value_slice_smooth {T : ℝ} (J : SmoothPlaneCurves T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : ContDiff ℝ ∞ (fun x => J.value (t,x)) := by
  apply contDiff_infty.mpr
  intro k
  rw [J.value_eq k ht]
  exact function_contDiff Plane ℝ k _

theorem value_continuousOn {T : ℝ} (J : SmoothPlaneCurves T) :
    ContinuousOn J.value (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
  have hc : ContinuousOn (fun p : ℝ × Plane => function Plane ℝ 0 (J.curve 0 p.1))
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    (functionMap Plane ℝ 0).continuous.comp_continuousOn
      ((J.smooth 0).continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1))
  exact (show Continuous (fun p : (Plane →ᵇ ℝ) × Plane => p.1 p.2) from continuous_eval).comp_continuousOn
    (hc.prodMk continuous_snd.continuousOn)

def timeDerivative {T : ℝ} (hT : 0 < T) (J : SmoothPlaneCurves T) : SmoothPlaneCurves T where
  curve k := derivWithin (J.curve k) (Icc (0 : ℝ) T)
  smooth k := (J.smooth k).derivWithin (uniqueDiffOn_Icc hT) (by simp)
  compatible := by
    intro k n hkn t ht
    let L := truncateCLM Plane ℝ k n hkn
    have hd := L.hasFDerivAt.comp_hasDerivWithinAt t
      (((J.smooth n).differentiableOn (by simp) t ht).hasDerivWithinAt)
    have hd' : HasDerivWithinAt (J.curve k)
        (L (derivWithin (J.curve n) (Icc (0 : ℝ) T) t)) (Icc (0 : ℝ) T) t :=
      hd.congr (fun s hs => (J.compatible k n hkn s hs).symm)
        (J.compatible k n hkn t ht).symm
    exact (hd'.derivWithin (uniqueDiffOn_Icc hT t ht)).symm

def spaceDerivative {T : ℝ} (J : SmoothPlaneCurves T) (j : Fin 2) : SmoothPlaneCurves T where
  curve k t := directionalDerivativeCLM Plane ℝ k (Pi.single j 1) (J.curve (k+1) t)
  smooth k := (directionalDerivativeCLM Plane ℝ k (Pi.single j 1)).contDiff.comp_contDiffOn
    (J.smooth (k+1))
  compatible := by
    intro k n hkn t ht
    rw [directionalDerivativeCLM_truncate,
      J.compatible (k+1) (n+1) (Nat.add_le_add_right hkn 1) t ht]

theorem value_spaceDerivative {T : ℝ} (J : SmoothPlaneCurves T) (j : Fin 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Plane) :
    (J.spaceDerivative j).value (t,x) = PlaneHeat.spatialPartial ℝ j (fun y => J.value (t,y)) x := by
  change function Plane ℝ 0 (directionalDerivativeCLM Plane ℝ 0 (Pi.single j 1) (J.curve 1 t)) x = _
  rw [function_directionalDerivativeCLM, ← J.value_eq 1 ht]
  rfl

theorem value_time_hasDerivWithinAt {T : ℝ} (hT : 0 < T) (J : SmoothPlaneCurves T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : Plane) :
    HasDerivWithinAt (fun s => J.value (s,x)) ((J.timeDerivative hT).value (t,x))
      (Icc (0 : ℝ) T) t := by
  let L : Space Plane ℝ 0 →L[ℝ] ℝ :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (functionMap Plane ℝ 0)
  exact L.hasFDerivAt.comp_hasDerivWithinAt t
    (((J.smooth 0).differentiableOn (by simp) t ht).hasDerivWithinAt)

def spatialDerivative {T : ℝ} (J : SmoothPlaneCurves T) (p : ℝ × Plane) : Plane →L[ℝ] ℝ :=
  ∑ j : Fin 2, (J.spaceDerivative j).value p • ContinuousLinearMap.proj j

def totalDerivative {T : ℝ} (hT : 0 < T) (J : SmoothPlaneCurves T) (p : ℝ × Plane) :
    (ℝ × Plane) →L[ℝ] ℝ :=
  ((J.timeDerivative hT).value p • (1 : ℝ →L[ℝ] ℝ)).coprod (J.spatialDerivative p)

theorem spatialDerivative_eq {T : ℝ} (J : SmoothPlaneCurves T)
    {p : ℝ × Plane} (hp : p ∈ Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :
    J.spatialDerivative p = fderiv ℝ (fun y => J.value (p.1,y)) p.2 := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
    ext j
    fin_cases j <;> simp
  rw [spatialDerivative, Fin.sum_univ_two, add_apply, smul_apply,
    smul_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.proj_apply,
    value_spaceDerivative J 0 hp.1, value_spaceDerivative J 1 hp.1]
  conv_rhs => rw [hv, map_add, map_smul, map_smul]
  simp only [PlaneHeat.spatialPartial, smul_eq_mul]
  ring

theorem spatialDerivative_continuousOn {T : ℝ} (J : SmoothPlaneCurves T) :
    ContinuousOn J.spatialDerivative (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
  continuousOn_finsetSum _ (fun j _ => (J.spaceDerivative j).value_continuousOn.smul continuousOn_const)

theorem totalDerivative_continuousOn {T : ℝ} (hT : 0 < T) (J : SmoothPlaneCurves T) :
    ContinuousOn (J.totalDerivative hT) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
  ((J.timeDerivative hT).value_continuousOn.smul continuousOn_const).continuousLinearMapCoprod
    J.spatialDerivative_continuousOn

theorem value_hasFDerivAt_interior {T : ℝ} (hT : 0 < T) (J : SmoothPlaneCurves T)
    {p : ℝ × Plane} (hp : p ∈ Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) :
    HasFDerivAt J.value (J.totalDerivative hT p) p := by
  have hc : p ∈ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) := ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩
  have htime : ∀ᶠ v : ℝ × Plane in 𝓝 p, HasFDerivAt (fun s => J.value (s,v.2))
      ((J.timeDerivative hT).value v • (1 : ℝ →L[ℝ] ℝ)) v.1 := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with v hv
    have hd := (J.value_time_hasDerivWithinAt hT ⟨hv.1.1.le,hv.1.2.le⟩ v.2).hasDerivAt
      (Icc_mem_nhds hv.1.1 hv.1.2)
    convert hd.hasFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro r
    simp [smul_eq_mul, mul_comm]
  have hspace : ∀ᶠ v : ℝ × Plane in 𝓝 p, HasFDerivAt (fun y => J.value (v.1,y))
      (J.spatialDerivative v) v.2 := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with v hv
    rw [J.spatialDerivative_eq ⟨⟨hv.1.1.le,hv.1.2.le⟩,hv.2⟩]
    exact ((J.value_slice_smooth ⟨hv.1.1.le,hv.1.2.le⟩).differentiable (by simp) v.2).hasFDerivAt
  exact (hasStrictFDerivAt_uncurry_coprod
    (u := p) (f := fun t x => J.value (t,x))
    (f₁ := fun t x => (J.timeDerivative hT).value (t,x) • (1 : ℝ →L[ℝ] ℝ))
    (f₂ := fun t x => J.spatialDerivative (t,x)) htime hspace
    (((J.timeDerivative hT).value_continuousOn.smul continuousOn_const).continuousAt
      (prod_mem_nhds (Icc_mem_nhds hp.1.1 hp.1.2) (show (univ : Set Plane) ∈ 𝓝 p.2 from univ_mem)))
    (J.spatialDerivative_continuousOn.continuousAt
      (prod_mem_nhds (Icc_mem_nhds hp.1.1 hp.1.2) (show (univ : Set Plane) ∈ 𝓝 p.2 from univ_mem)))).hasFDerivAt

theorem value_hasFDerivWithinAt {T : ℝ} (hT : 0 < T) (J : SmoothPlaneCurves T)
    {p : ℝ × Plane} (hp : p ∈ Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :
    HasFDerivWithinAt J.value (J.totalDerivative hT p) (Icc (0 : ℝ) T ×ˢ univ) p := by
  have hc : closure (Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)) = Icc (0 : ℝ) T ×ˢ univ := by
    rw [closure_prod_eq, closure_Ioo hT.ne, closure_univ]
  have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set Plane) ⊆ Icc (0 : ℝ) T ×ˢ univ :=
    prod_mono Ioo_subset_Icc_self (Subset.refl _)
  have he : (fun q => fderiv ℝ J.value q) =ᶠ[𝓝[Ioo (0 : ℝ) T ×ˢ (univ : Set Plane)] p]
      J.totalDerivative hT := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (J.value_hasFDerivAt_interior hT hq).fderiv
  have hd := hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun q hq => (J.value_hasFDerivAt_interior hT hq).differentiableAt.differentiableWithinAt)
    ((convex_Ioo (0 : ℝ) T).prod convex_univ) (isOpen_Ioo.prod isOpen_univ)
    (fun q hq => (J.value_continuousOn q (hc ▸ hq)).mono hsub)
    (((J.totalDerivative_continuousOn hT p hp).mono hsub).congr' he.symm)
  rwa [hc] at hd

theorem value_contDiffOn {T : ℝ} (hT : 0 < T) (J : SmoothPlaneCurves T) :
    ContDiffOn ℝ ∞ J.value (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
  have hi (n : ℕ) : ∀ J : SmoothPlaneCurves T,
      ContDiffOn ℝ n J.value (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
    induction n with
    | zero => exact fun K => contDiffOn_zero.mpr K.value_continuousOn
    | succ n ih =>
      intro K
      rw [Nat.cast_add, Nat.cast_one]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ)).mpr
      refine ⟨by simp, K.totalDerivative hT, ?_, fun p hp => K.value_hasFDerivWithinAt hT hp⟩
      change ContDiffOn ℝ (n : ℕ∞ω) (fun p =>
        ((K.timeDerivative hT).value p • (1 : ℝ →L[ℝ] ℝ)).coprod
          (K.spatialDerivative p)) _
      simp only [← ContinuousLinearMap.comp_fst_add_comp_snd]
      exact (((ih (K.timeDerivative hT)).smul contDiffOn_const).clm_comp contDiffOn_const).add
        ((ContDiffOn.sum (fun j _ =>
          (ih (K.spaceDerivative j)).smul contDiffOn_const)).clm_comp contDiffOn_const)
  exact contDiffOn_infty.mpr (fun n => hi n J)

end SmoothPlaneCurves
end ForcedComputation.BoundedSpatialJets

end

end OAI

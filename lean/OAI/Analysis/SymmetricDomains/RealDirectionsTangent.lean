import Mathlib
import OAI.Analysis.SymmetricDomains.ForwardBackwardGerm

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology
open scoped Classical

theorem support_along_chart_fderiv
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {d : ℕ}
    (h : H → ℂ) (f : E → H) (g : H → E) (q : (Fin d → ℝ) → H)
    {x : Fin d → ℝ} (hg0 : g (q x)=0) (hg : DifferentiableAt ℝ g (q x))
    (hq : DifferentiableAt ℝ q x)
    (hfgq : (f ∘ g ∘ q) =ᶠ[𝓝 x] q)
    (hlog : AnalyticAt ℂ (fun z => Complex.log (h (f z))) 0) :
    fderiv ℝ (fun y => Real.log ‖h (q y)‖) x =
      (fderiv ℝ (fun z => Real.log ‖h (f z)‖) 0).comp (fderiv ℝ (g ∘ q) x) := by
  have hr : DifferentiableAt ℝ (fun z => Real.log ‖h (f z)‖) 0 := by
    have hh := Complex.reCLM.differentiableAt.comp 0 (hlog.differentiableAt.restrictScalars ℝ)
    simpa only [Function.comp_def,Complex.reCLM_apply,Complex.log_re] using hh
  have hD : DifferentiableAt ℝ (fun z => Real.log ‖h (f z)‖) ((g ∘ q) x) := by
    simpa only [Function.comp_apply,hg0] using hr
  have hh := hD.hasFDerivAt.comp x (hg.comp x hq).hasFDerivAt
  have he : (fun y => Real.log ‖h (q y)‖) =ᶠ[𝓝 x]
      ((fun z => Real.log ‖h (f z)‖) ∘ (g ∘ q)) := by
    filter_upwards [hfgq] with y hy
    exact congrArg (fun z => Real.log ‖h z‖) hy.symm
  have hh' := hh.congr_of_eventuallyEq he
  simpa only [Function.comp_apply,hg0] using hh'.fderiv
end

open Set Filter Topology Metric
open scoped Classical
namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}

theorem oldOffsetDerivative_kernel_range (c : NashBoundaryChart (m := m) U V B q) {x}
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1))) :
    LinearMap.ker (c.oldOffsetDerivative (c.normal.parameters x)).toLinearMap =
      LinearMap.range (fderiv ℝ (fun y => c.chart.projection (q y-q c.center)) x).toLinearMap := by
  let f := fun y => c.chart.projection (q y-q c.center)
  let M := fderiv ℝ f x
  let D := c.oldOffsetDerivative (c.normal.parameters x)
  have hf : DifferentiableAt ℝ f x := (c.chart.projection.restrictScalars ℝ).differentiableAt.comp x (hq.sub_const (q c.center))
  have hD : HasFDerivAt c.oldOffset D (f x) := by
    dsimp only [f]
    rw [←c.oldPosition_projection hgood]
    exact c.oldOffset_hasFDerivAt hgood.2.1
  have hz : D.comp M=0 :=
    ((hD.comp x hf.hasFDerivAt).congr_of_eventuallyEq (c.oldOffset_projection_germ hgood).symm).unique (hasFDerivAt_const (0 : Fin c.normal.normalDim → ℝ) x)
  have hle : LinearMap.range M.toLinearMap ≤ LinearMap.ker D.toLinearMap := by
    rintro _ ⟨v,rfl⟩
    exact congrArg (fun L : (Fin d → ℝ) →L[ℝ] (Fin c.normal.normalDim → ℝ) => L v) hz
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hMi := (c.projection_tangent_generic hgood hq hqi hr).1
  have hMd : Module.finrank ℝ (LinearMap.range M.toLinearMap)=d := by
    simpa only [Module.finrank_pi,Fintype.card_fin] using LinearMap.finrank_range_of_inj hMi
  have hDD := D.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (c.oldOffsetDerivative_surjective _),finrank_top] at hDD
  have hdim : Module.finrank ℝ (Affine m)=2*m := by simp [Affine,Module.finrank_pi_fintype,Nat.mul_comm]
  simp only [Module.finrank_pi,Fintype.card_fin,hdim] at hDD
  rw [hMd]
  have hc := c.normal.complex_dimension
  have hd := c.normal.real_dimension
  omega
end NashBoundaryChart

namespace NashBoundaryScalingChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N} {c : NashBoundaryChart (m := m) U V B q}
variable {x : Fin d → ℝ}

theorem real_directions_tangent (s : NashBoundaryScalingChart c x)
    (hgood : c.GoodAt x) (hq : DifferentiableAt ℝ q x)
    (hqi : Function.Injective (fderiv ℝ q x))
    (hr : m ≤ Matrix.rank (fun j i => fderiv ℝ (fun y => q y j) x (Pi.single i 1)))
    (z : Affine s.tangentDim) (w : Fin s.normalDim → ℝ) :
    ∃ v, fderiv ℝ (s.backward ∘ q) x v = (z,fun i => (w i : ℂ)) := by
  let y : Affine s.tangentDim × Affine s.normalDim := (z,fun i => (w i : ℂ))
  have hy : s.coordinates.symm y ∈ LinearMap.ker (c.oldOffsetDerivative (c.normal.parameters x)).toLinearMap := by
    change c.oldOffsetDerivative (c.normal.parameters x) (s.coordinates.symm y) = 0
    rw [s.differential]
    have he : Flatten.imaginaryPart s.normalDim y.2 = 0 := by ext i; simp [y,Flatten.imaginaryPart]
    rw [he,map_zero]
  rw [c.oldOffsetDerivative_kernel_range hgood hq hqi hr] at hy
  obtain ⟨v,hv⟩ := hy
  refine ⟨v,?_⟩
  let f := fun y => c.chart.projection (q y-q c.center)
  have hf : DifferentiableAt ℝ f x := (c.chart.projection.restrictScalars ℝ).differentiableAt.comp x (hq.sub_const (q c.center))
  have hd : fderiv ℝ (s.backward ∘ q) x =
      (s.coordinates.toContinuousLinearMap.restrictScalars ℝ).comp (fderiv ℝ f x) := by
    exact ((s.coordinates.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp x
      (hf.hasFDerivAt.sub_const (c.oldPosition (c.normal.parameters x)))).fderiv
  rw [hd,ContinuousLinearMap.comp_apply]
  change s.coordinates (fderiv ℝ f x v)=y
  rw [show fderiv ℝ f x v=s.coordinates.symm y from hv,s.coordinates.apply_symm_apply]
end NashBoundaryScalingChart
end Release061

end

end OAI

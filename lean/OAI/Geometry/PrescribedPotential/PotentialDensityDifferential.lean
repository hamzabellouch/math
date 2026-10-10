import Mathlib
import OAI.Geometry.PrescribedPotential.CompletedVolume
import OAI.Geometry.PrescribedPotential.NonlinearHessianCommutator
import OAI.Geometry.PrescribedPotential.PotentialDensity
import OAI.Geometry.PrescribedPotential.SmoothPotentialDifference

namespace OAI

/-! Potential Density Differential. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric
local instance matrixContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (ContinuousSMul ℝ (Fin n → Fin n → ℂ))

lemma potentialDensity_directional_at (g : KaehlerMetric A) (φ ψ : SmoothRealFunction A)
    (q : Fin A.count) {x : X} (hx : x ∈ (A.chart q).source) :
    HasDerivAt (fun t : ℝ => ((g.potentialDensity (φ.addFunction (ψ.realSMul t))).value x : ℂ))
      ((g.matrix q (A.chart q x)).det⁻¹ *
        NonlinearHessian.detDifferential (g.matrix q (A.chart q x) + φ.hessian q (A.chart q x))
          (ψ.hessian q (A.chart q x))) 0 := by
  let M := g.matrix q (A.chart q x) + φ.hessian q (A.chart q x)
  let N := ψ.hessian q (A.chart q x)
  have hc := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add M
  simp only [one_smul] at hc
  have hM : HasFDerivAt Matrix.det (NonlinearHessian.detDifferential M) (M+(0 : ℝ) • N) := by
    simpa only [zero_smul,add_zero] using NonlinearHessian.detDifferential_hasFDeriv M
  have hd := (hM.comp_hasDerivAt (0 : ℝ) hc).const_mul (g.matrix q (A.chart q x)).det⁻¹
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with t
  rw [g.potentialDensity_complex _ q hx]
  unfold volumePolynomial
  rw [SmoothRealFunction.hessian_addFunction _ _ q ((A.chart q).mapsTo hx),
    SmoothRealFunction.hessian_realSMul]
  have hs : t • N = (t : ℂ) • N := by
    ext i j
    exact Complex.real_smul
  simp only [Function.comp_apply, id_eq] at *
  rw [hs,div_eq_mul_inv,mul_comm]
  congr 1
  simp only [M,N,add_assoc]

end KaehlerMetric
end Anticanonical.SourceSmooth

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma completedVolumeDerivative_source (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (φ ψ : SmoothRealFunction A) (q : Fin A.count) {x : X} (hx : x ∈ (A.chart q).source) :
    D.localizers.strong (k : ℝ)
      (fderiv ℝ (D.completedVolume k hk) (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ))
        (D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal ψ))) x =
      (g.matrix q (A.chart q x)).det⁻¹ *
        NonlinearHessian.detDifferential (g.matrix q (A.chart q x) + φ.hessian q (A.chart q x))
          (ψ.hessian q (A.chart q x)) := by
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  let u := D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal φ)
  let v := D.localizers.embed ((k : ℝ)+2) (Smooth.ofReal ψ)
  let E : D.localizers.Sobolev (k : ℝ) →L[ℝ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (D.localizers.strong (k : ℝ))
  have hc := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u
  simp only [one_smul] at hc
  have hu : HasFDerivAt (D.completedVolume k hk)
      (fderiv ℝ (D.completedVolume k hk) u) (u+(0 : ℝ) • v) := by
    simpa only [zero_smul,add_zero] using
      ((D.completedVolume_contDiff k hk).differentiable (by simp) u).hasFDerivAt
  have hd := E.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hu.comp_hasDerivAt (0 : ℝ) hc)
  have he (t : ℝ) : u+t • v = D.localizers.embed ((k : ℝ)+2)
      (Smooth.ofReal (φ.addFunction (ψ.realSMul t))) := by
    dsimp only [u,v]
    rw [← map_smul,← map_add]
    congr 1
    apply Smooth.ext
    intro y
    simp [SmoothRealFunction.addFunction,SmoothRealFunction.realSMul,Complex.real_smul]
  have hp := g.potentialDensity_directional_at φ ψ q hx
  apply hd.unique
  apply hp.congr_of_eventuallyEq
  filter_upwards [] with t
  change E (D.completedVolume k hk (u+t • v)) = _
  rw [he,D.completedVolume_embed]
  change D.localizers.strong (k : ℝ) (D.localizers.embed (k : ℝ) _) x = _
  rw [D.localizers.strong_embed _ hs]
  rfl

end GluingData
end GlobalElliptic

end
end

end OAI

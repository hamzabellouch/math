import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport

namespace OAI

/-! Smooth Potential Difference. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace SmoothRealFunction

def addFunction (φ ψ : SmoothRealFunction A) : SmoothRealFunction A where
  value x := φ.value x + ψ.value x
  smooth i := (φ.smooth i).add (ψ.smooth i)

lemma hessian_addFunction (φ ψ : SmoothRealFunction A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (φ.addFunction ψ).hessian i z = φ.hessian i z + ψ.hessian i z := by
  have hφ := (φ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)
  have hψ := (ψ.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)
  change ContDiffAt ℝ ∞ (φ.localExpression i) z at hφ
  change ContDiffAt ℝ ∞ (ψ.localExpression i) z at hψ
  change PotentialKaehler.hermitianPartMatrix
    (fderiv ℝ (fderiv ℝ (φ.localExpression i + ψ.localExpression i)) z) = _
  rw [EllipticKernel.hessian_add hφ hψ, EllipticKernel.hermitianPartMatrix_add]
  rfl

def difference (φ ψ : SmoothRealFunction A) : SmoothRealFunction A :=
  φ.addFunction (ψ.realSMul (-1))

lemma difference_value (φ ψ : SmoothRealFunction A) (x : X) :
    (φ.difference ψ).value x = φ.value x - ψ.value x := by
  change φ.value x + -1 * ψ.value x = _
  ring

lemma hessian_difference (φ ψ : SmoothRealFunction A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) :
    (φ.difference ψ).hessian i z = φ.hessian i z - ψ.hessian i z := by
  rw [difference, hessian_addFunction φ _ i hz, hessian_realSMul]
  simp [sub_eq_add_neg]
end SmoothRealFunction
end Anticanonical.SourceSmooth

end
end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexFactorParameters
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothComplexWeightFactors
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothExponentialDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothLocalSection
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieProductDifferential

namespace OAI

/-! # Smooth local coordinates from the complex-weight factors -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff Topology

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

def kernelParameter : E →L[ℝ] F.N.modelSpace :=
  (show E →ₗ[ℝ] F.N.modelSpace from
    F.N.equiv.toLinearMap.comp (T.kernelComponent H)).toContinuousLinearMap

def cartanParameter : E →L[ℝ] F.D.modelSpace :=
  (show E →ₗ[ℝ] F.D.modelSpace from
    F.D.equiv.toLinearMap.comp (T.cartanComponent H)).toContinuousLinearMap

def factorParameter (x : E) : G :=
  F.inclusionN (F.ExpN (F.kernelParameter x)) *
    F.inclusionD (F.ExpD (F.cartanParameter x))

theorem factorParameter_zero : F.factorParameter 0 = 1 := by
  unfold factorParameter
  rw [map_zero,map_zero]
  have hn : F.ExpN (0 : F.N.modelSpace) = 1 := F.isExpN.map_zero
  have hd : F.ExpD (0 : F.D.modelSpace) = 1 := F.isExpD.map_zero
  rw [hn,hd,map_one,map_one,mul_one]

theorem contMDiff_factorParameter (hExp : IsGroupExponential Exp) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ F.factorParameter := by
  have hn := F.contMDiff_expN.comp F.kernelParameter.contDiff.contMDiff
  have hd := F.contMDiff_expD.comp F.cartanParameter.contDiff.contMDiff
  exact ((F.contMDiff_inclusionN hExp).comp hn).mul ((F.contMDiff_inclusionD hExp).comp hd)

theorem factorParameter_line (v : E) (t : ℝ) :
    F.factorParameter (t • v) =
      Exp (t • (T.kernelComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G)) *
        Exp (t • (T.cartanComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G)) := by
  change F.inclusionN (F.ExpN (F.N.equiv (T.kernelComponent H (t • v)))) *
    F.inclusionD (F.ExpD (F.D.equiv (T.cartanComponent H (t • v)))) = _
  rw [F.compatibleN,F.compatibleD]
  exact congrArg₂ (fun x y : GroupLieAlgebra (𝓘(ℝ, E)) G => Exp x * Exp y)
    (congrArg Subtype.val ((T.kernelComponent H).map_smul t v))
    (congrArg Subtype.val ((T.cartanComponent H).map_smul t v))

theorem hasMFDerivAt_factorParameter_line (hExp : IsGroupExponential Exp) (v : E) :
    HasMFDerivAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,E)) (fun t : ℝ => F.factorParameter (t • v)) 0
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v) := by
  rw [show (fun t : ℝ => F.factorParameter (t • v)) =
      (fun t => Exp (t • (T.kernelComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G)) *
        Exp (t • (T.cartanComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G))) from
    funext (F.factorParameter_line v)]
  have hc := PolycyclicRecognition.HasMFDerivAt.mul_at_one
    (hExp.hasMFDerivAt_zero (T.kernelComponent H v))
    (hExp.hasMFDerivAt_zero (T.cartanComponent H v))
    (by rw [zero_smul,hExp.map_zero]) (by rw [zero_smul,hExp.map_zero])
  have hd : (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      (T.kernelComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G) +
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      (T.cartanComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G)) =
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v := by
    apply ContinuousLinearMap.ext
    intro t
    change t • (T.kernelComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G) +
      t • (T.cartanComponent H v : GroupLieAlgebra (𝓘(ℝ,E)) G) = t • v
    rw [← smul_add]
    exact congrArg (fun x : GroupLieAlgebra (𝓘(ℝ, E)) G => t • x)
      (T.factorComponents_add H v)
  exact hc.congr_mfderiv hd

theorem hasMFDerivAt_factorParameter (hExp : IsGroupExponential Exp) :
    HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) F.factorParameter 0
      (ContinuousLinearMap.id ℝ E) := by
  apply hasMFDerivAt_zero_of_smooth_linear_curves _ (F.contMDiff_factorParameter hExp).contMDiffAt
  intro v
  exact F.hasMFDerivAt_factorParameter_line hExp v

theorem exists_smooth_factorSection (hExp : IsGroupExponential Exp) :
    ∃ r : G → E, ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ r 1 ∧ r 1 = 0 ∧
      ∀ᶠ g in 𝓝 (1 : G), F.factorParameter (r g) = g := by
  have h := exists_smooth_local_section (d := ContinuousLinearEquiv.refl ℝ E)
    (F.contMDiff_factorParameter hExp).contMDiffAt (F.hasMFDerivAt_factorParameter hExp)
  simpa only [F.factorParameter_zero] using h

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI

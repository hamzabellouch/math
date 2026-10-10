import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Recursion.AssemblyDescriptorList
import OAI.MeasureTheory.FalconerCompletion.Shells.WeightedMaskTransform

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

noncomputable def assemblyEndpointSmooth (e : RecursiveEnvironmentND n)
    (x : EuclideanSpace ℝ (Fin (n+1))) (b : PolicyDescriptor) :
    Attempt4PrefixShell.SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))) :=
  ⟨fun w => (actualEndpointMask e.ρ e.mass e.N e.sig e.C e.J 0 b x w:ℂ),
    Complex.ofRealCLM.contDiff.comp (actualEndpointMask_smooth _ _ _ _ _ _ _ _ _)⟩

noncomputable def assemblyDistanceTransform (e₁ e₂ : RecursiveEnvironmentND n) (c : ℕ)
    (X Y : Set (EuclideanSpace ℝ (Fin (n+1))))
    (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (r : ℝ) : ℂ :=
  Attempt4PrefixShell.weightedMaskTransformND
    (assemblyDescriptorList e₁.profile e₁.N e₁.q c)
    (assemblyDescriptorList e₂.profile e₂.N e₂.q c)
    (assemblyEndpointSmooth e₁) (assemblyEndpointSmooth e₂) f g e₁.ρ e₂.ρ X Y
    (((2:ℝ)^e₁.N)^(-e₁.mass 0)) (((2:ℝ)^e₂.N)^(-e₂.mass 0)) 0 r
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI

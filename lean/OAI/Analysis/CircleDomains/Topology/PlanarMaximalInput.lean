import OAI.Analysis.CircleDomains.Sobolev.SourceArea
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-!
# Published planar L² maximal input

T. Tao, *Lecture Notes 3 for Math 247A*, Fall 2006, Proposition 1.1,
p. 1, https://www.math.ucla.edu/~tao/247a.1.06f/notes3.pdf.
The dimension-two, p=2 strong maximal inequality is used. We retain a finite nonnegative
representative of the maximal function; modifying it on its null set
of infinite values leaves each fixed-radius average bound valid almost
everywhere. Squaring the norm bound gives the energy inequality below.
-/
open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 def PlanarMaximalL2 : Prop :=
  ∃ A : ℝ, 0 < A ∧ ∀ g : ℂ → ℝ, MemLp g 2 volume →
    ∃ m : ℂ → ℝ, Measurable m ∧ (∀ z, 0 ≤ m z) ∧ MemLp m 2 volume ∧
      (∫ z, m z^2) ≤ A^2*(∫ z, g z^2) ∧
      ∀ r : ℝ, 0 < r → ∀ᵐ x ∂volume,
        (∫ y in ball x r, ‖g y‖) ≤ volume.real (ball x r)*m x

end CircleDomainRigidity

end

end OAI

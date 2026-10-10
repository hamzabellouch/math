import OAI.Analysis.LipschitzHilbert.Fourier.SharpKernelComparison

namespace OAI

/-! The additional classical one-dimensional input needed only for the
horizontal remainder. Grafakos, Classical Fourier Analysis, 3rd edition,
GTM 249, Springer (2014), Theorem 5.1.12, printed p.323 (PDF p.338),
DOI 10.1007/978-1-4939-1194-3. The maximal Hilbert bound gives this smaller
consequence for differences of two inner truncations. The factor pi from
the book's normalization is absorbed in C. Only p=3/2 and p=4 are used.
This is an explicit proposition, not an axiom or an asserted proof. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert

def oneDimensionalTruncatedHilbert (r R : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ t, PacketRepresentation.sharpTimeKernel r R t*f (x-t)

def HorizontalHilbertInput : Prop :=
  ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, p=3/2 ∨ p=4 →
    ∀ r R : ℝ, 0<r → r≤R → ∀ f : SchwartzMap ℝ ℂ,
      Integrable (fun x => ‖oneDimensionalTruncatedHilbert r R f x‖^p) ∧
      (∫ x, ‖oneDimensionalTruncatedHilbert r R f x‖^p)≤C^p*(∫ x, ‖f x‖^p)

end LipschitzHilbert

end

end OAI

import OAI.Analysis.LipschitzHilbert.Estimates.NormalizedLatticeAverage

namespace OAI

/-! The actual common finite convolution form, named independently of
its estimate and of the lattice used to average it. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

def latticeLength (topLength : ℝ) (labels : ∀ j, Finset (Label j))
    (i : LatticeRow labels) : ℝ := topLength/(2:ℝ)^i.1.val

theorem latticeLength_pos (topLength : ℝ) (htop : 0<topLength)
    (labels : ∀ j, Finset (Label j)) (i : LatticeRow labels) :
    0<latticeLength topLength labels i := div_pos htop (pow_pos (by norm_num) _)

def latticeFrequencyWindow (chi : SchwartzMap (ℝ×ℝ) ℂ) (topLength width : ℝ)
    (htop : 0<topLength) (hwidth : 0<width) (labels : ∀ j, Finset (Label j))
    (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (i : LatticeRow labels) (k : κ) : SchwartzMap (ℝ×ℝ) ℂ :=
  scaledFrequencyWindow (planarInverseSchwartz chi) (latticeLength topLength labels i)
    width (theta i.1 i.2) (2*Real.pi*center k)
    (latticeLength_pos topLength htop labels i).ne' hwidth.ne'

def normalizedConvolutionSum (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (topLength width : ℝ) (htop : 0<topLength) (hwidth : 0<width)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (b : ∀ j, labels j → κ → ℝ → ℂ) (u : ℝ×ℝ → ℝ)
    (f g : ℝ×ℝ → EuclideanSpace ℂ κ) : ℂ :=
  ∑ i : LatticeRow labels, ∑ k, ∫ z, b i.1 i.2 k (u z)*
    kernelConvolution
      (horizontalFrequencyKernel (latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k)
        nu q (latticeLength topLength labels i) (theta i.1 i.2))
      (kernelConvolution
        (verticalFrequencyKernel (latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i k)
          nu q width (center k)) (fun x => f x k)) z*star (g z k) ∂volume.prod volume

end LipschitzHilbert.PacketRepresentation

end

end OAI

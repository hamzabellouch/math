import OAI.Analysis.LipschitzHilbert.Fourier.AnnularSlopePartition
import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedBandFormL1
import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedFrequencyL1

namespace OAI

/-! The arithmetic slope partition recombines exactly into the finite
vector-valued diagonal band operator. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

def finiteDiagonalBandL1 {N : ℕ} {κ : Type} [Fintype κ]
    (psi beta : SchwartzMap ℝ ℂ) (topLength width : ℝ) (center : κ → ℝ)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) : ℂ :=
  ∑ j : Fin N, ∑ k, ∫ z, variableFrequencyMultiplierL1
    (annularBandSymbol psi beta (topLength/(2:ℝ)^j.val) width (center k) u) (f k) z*
    star (g z k) ∂planeMeasure

theorem finitePartitionedBand_eq_diagonal_l1 {N : ℕ} {κ : Type} [Fintype κ]
    (psi beta : SchwartzMap ℝ ℂ) (K : Fin N → ℕ)
    (topLength width w delta c M B U : ℝ)
    (htop : 0<topLength) (hwidth : 0<width) (hw : 0<w) (hd : 0<delta) (hc : 0<c) (hM : 0≤M)
    (hbetaSupport : ∀ s, beta s≠0 → |s|≤B)
    (center : κ → ℝ) (hpsi : ∀ s : ℝ, psi s≠0 → |s|≤M)
    (hbeta : ∀ k eta, beta (symbolY width eta (center k))≠0 → c≤w*eta)
    (hK : ∀ j, U/(delta*(w/(topLength/(2:ℝ)^j.val)))+M/(delta*c)≤K j)
    (u : ℝ×ℝ → ℝ) (hum : Measurable u) (hu : ∀ z, |u z|≤U)
    (f : κ → (ℝ×ℝ) → ℂ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (hf : ∀ k, Integrable (f k) planeMeasure)
    (hg : ∀ k, Integrable (fun z => g z k) planeMeasure) :
    finitePartitionedBandL1 psi (scaledSlopePartition delta hd) beta topLength width w
      (fun j => finiteSlopeLabels (K j))
      (fun j n => finiteSlopeCenter (K j) delta (w/(topLength/(2:ℝ)^j.val)) n.val)
      center u f g=finiteDiagonalBandL1 (N:=N) psi beta topLength width center u f g := by
  classical
  unfold finitePartitionedBandL1 finiteDiagonalBandL1
  dsimp only [LatticeRow]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hlen : 0<topLength/(2:ℝ)^j.val := div_pos htop (pow_pos (by norm_num) _)
  exact recombine_partitioned_frequency_pairing_l1 psi (scaledSlopePartition delta hd) beta
    (topLength/(2:ℝ)^j.val) width w (center k) M B U
    (fun n : finiteSlopeLabels (K j) =>
      finiteSlopeCenter (K j) delta (w/(topLength/(2:ℝ)^j.val)) n.val) hlen hwidth hpsi hbetaSupport u hum hu
    (finiteSlopePartition_annular psi beta (K j) (topLength/(2:ℝ)^j.val) width w delta c M U
      (center k) hlen hw hd hc hM hpsi (hbeta k) (hK j) u hu) (f k) (hf k) (fun z => g z k) (hg k)

end LipschitzHilbert.PacketRepresentation

end

end OAI

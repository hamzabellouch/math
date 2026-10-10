import OAI.Analysis.LipschitzHilbert.Fourier.AnnularFrequencyEnvelope

namespace OAI

/-! Finite slope recombination for L1 inputs, with all frequency
interchanges justified by the compact annular envelope. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem recombine_partitioned_frequency_pairing_l1 {ι : Type*} [Fintype ι]
    (psi rho beta : SchwartzMap ℝ ℂ) (l W w center M B U : ℝ) (theta : ι → ℝ)
    (hl : 0<l) (hW : 0<W)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (u : ℝ×ℝ → ℝ) (hu : Measurable u) (hub : ∀ z, |u z|≤U)
    (hpartition : ∀ z omega : ℝ×ℝ,
      psi (l*(omega.1+u z*omega.2))≠0 → beta (symbolY W omega.2 center)≠0 →
      ∑ i, rho (-symbolX l omega.1 omega.2 (theta i)/(w*omega.2))=1)
    (f : ℝ×ℝ → ℂ) (hf : Integrable f planeMeasure)
    (g : ℝ×ℝ → ℂ) (hg : Integrable g planeMeasure) :
    (∑ i, ∫ z, variableFrequencyMultiplierL1
      (partitionedFrequencySymbol psi rho beta l W w (theta i) center u) f z*star (g z) ∂planeMeasure)=
      ∫ z, variableFrequencyMultiplierL1 (annularBandSymbol psi beta l W center u) f z*star (g z) ∂planeMeasure := by
  classical
  have henv (i : ι) := exists_partitionedFrequencySymbol_envelope psi rho beta
    l W w (theta i) center M B U hl hW ((abs_nonneg (u 0)).trans (hub 0)) hpsi hbeta u hub
  choose q hq hbound using henv
  rw [finite_variableFrequencyMultiplier_pairing_l1
    (fun i => partitionedFrequencySymbol psi rho beta l W w (theta i) center u)
    (fun i => partitionedFrequencySymbol_measurable psi rho beta l W w (theta i) center u hu)
    q hq hbound f hf g hg,
    sum_partitionedFrequencySymbol psi rho beta l W w center theta u hpartition]

end LipschitzHilbert.PacketRepresentation

end

end OAI

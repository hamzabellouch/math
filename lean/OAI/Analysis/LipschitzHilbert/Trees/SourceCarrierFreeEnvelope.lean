import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceLattice
import OAI.Analysis.LipschitzHilbert.Fourier.TileEnvelopeKernel

namespace OAI

/-! The positive error envelope must not inherit the large carrier bound
of the wide reference cone. The exact raw norm is independent of it. -/

noncomputable section
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem raw_joint_measurable (P : SourceLatticePacket N κ ι)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) :
    Measurable (fun z : ℝ×ℝ => P.raw i j u k z.1 z.2) :=
  (modulatedPlanarJet_continuous (P.profile j u k) (P.actualX j u) (P.actualZ j u)
    (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale
    (P.length_pos j).ne' i).measurable

theorem raw_swapped_joint_measurable (P : SourceLatticePacket N κ ι)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) :
    Measurable (fun z : ℝ×ℝ => P.raw i j u k z.2 z.1) := by
  intro s hs
  change MeasurableSet (Prod.swap ⁻¹'
    ((fun z : ℝ×ℝ => P.raw i j u k z.1 z.2) ⁻¹' s))
  exact (measurable_swap : Measurable (Prod.swap : ℝ×ℝ → ℝ×ℝ))
    ((P.raw_joint_measurable i j u k) hs)

/-- The absolute raw-envelope constant contains no frequency or carrier. -/
def absoluteConstant (P : SourceLatticePacket N κ ι) : ℝ :=
  ((2^P.order*P.profileBound)*P.ratioBound^2)*3^(2*P.order)

theorem absoluteConstant_pos (P : SourceLatticePacket N κ ι) : 0 < P.absoluteConstant := by
  have hR : 0 < P.ratioBound := zero_lt_one.trans_le P.ratioBound_ge_one
  have hB := P.profileBound_pos
  unfold absoluteConstant
  positivity

theorem raw_absolute_lattice_envelope (P : SourceLatticePacket N κ ι)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤ P.absoluteConstant*
      (lineEnvelope (P.length j*(P.snappedSite j u).1) (P.length j) P.order x*
        lineEnvelope (P.width*(P.snappedSite j u).2) P.width P.order y) := by
  apply (P.raw_absolute_envelope i j u k y x).trans
  have hB := P.profileBound_pos
  have hA : 0 ≤ (2^P.order*P.profileBound)*P.ratioBound^2 := by positivity
  have h := mul_le_mul_of_nonneg_left (P.snapped_envelope j u y x) hA
  simpa only [absoluteConstant,mul_assoc] using h

/-- This is the envelope used by the original positive angular-error
convolution estimate, on the original snapped lattice. -/
theorem raw_absolute_tileEnvelope (P : SourceLatticePacket N κ ι) (horder : 6 ≤ P.order)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (z : ℝ×ℝ) :
    ‖P.raw i j u k z.2 z.1‖ ≤ P.absoluteConstant*
      tileEnvelope (P.length j*(P.snappedSite j u).1)
        (P.width*(P.snappedSite j u).2) (P.length j) P.width 6 z := by
  apply (P.raw_absolute_lattice_envelope i j u k z.2 z.1).trans
  apply mul_le_mul_of_nonneg_left _ P.absoluteConstant_pos.le
  exact mul_le_mul (lineEnvelope_antitone _ _ _ horder)
    (lineEnvelope_antitone _ _ _ horder) (lineEnvelope_nonneg _ _ _ _)
    (lineEnvelope_nonneg _ _ _ _)

end LipschitzHilbert.SourceLatticePacket

end

end OAI

import OAI.InformationTheory.Entanglement.ProjectionStats
import OAI.InformationTheory.Entanglement.CorrelationBound
import OAI.InformationTheory.Entanglement.SparseSeparable

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace ProjectionCriterion
open ChannelCompletion TensorCriterion
variable {Q K D I : Type} [Fintype Q] [Fintype K] [Fintype D] [Fintype I]
  [DecidableEq Q] [DecidableEq K] [DecidableEq D] [DecidableEq I]
  [Nonempty Q] [Nonempty K] [Nonempty D]

namespace Data
variable (d : Data Q K D I)
lemma C_nonseparable : ¬ Separable d.C := by
  intro hsep
  have hu := separable_compression_bound hsep d.κ (fun J hJ => d.clique J (by
    simpa only [d.C_diag] using hJ))
  have ht : compressionTrace d.C=(Fintype.card Q : ℝ)*(Fintype.card D : ℝ) := by
    change (Matrix.trace d.B).re = _
    rw [d.B_trace]
    simp
  have hs : compressionSum d.C=(∑ q, ∑ r, (correlation d.u q r)^2)*(Fintype.card D : ℝ) := by
    change (∑ i, ∑ j, d.B i j).re = _
    rw [d.B_sum]
    simp [-Complex.ofReal_pow]
  rw [ht,hs] at hu
  have hD : 0 < (Fintype.card D : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hQ : 0 < (Fintype.card Q : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hlo := mul_le_mul_of_nonneg_right (correlation_lower d.u d.unit) hD.le
  have hhi := mul_lt_mul_of_pos_right d.gap (mul_pos hQ hD)
  have he : (Fintype.card Q : ℝ)/Fintype.card K*
      ((Fintype.card Q : ℝ)*Fintype.card D) =
      (Fintype.card Q : ℝ)^2/Fintype.card K*Fintype.card D := by ring
  rw [he] at hhi
  exact (not_lt_of_ge (hlo.trans hu)) hhi
end Data

theorem rectangular_projection_criterion (d : Data Q K D I) :
    PPT d.Psi ∧ PPT (hsAdjoint d.Psi) ∧ ¬ Separable d.C ∧
      Matrix.trace d.C=(Fintype.card Q : ℂ)^2*(Fintype.card D : ℂ) := by
  exact ⟨d.Psi_ppt,d.adjoint_ppt,d.C_nonseparable,d.C_trace⟩

end ProjectionCriterion

end

end OAI

import Mathlib
import OAI.Analysis.AffineBernstein.MatrixMetric

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- Every coefficient of these covectors is positive, so their affine caps
are uniformly bounded in the orthant model. -/
def capTiltedCovector (r : ι) (i : ι) : ℝ := 1 + (Pi.single r (1:ℝ) : ι → ℝ) i

lemma inverse_trace_tilted_identity (A : Matrix ι ι ℝ) :
    (∑ r, inverseMatrixPair A (capTiltedCovector r) (capTiltedCovector r)) =
      A⁻¹.trace + ((Fintype.card ι:ℝ)+2)*inverseMatrixPair A (fun _ => 1) (fun _ => 1) := by
  have hd (r : ι) : inverseMatrixPair A (Pi.single r 1) (Pi.single r 1) = A⁻¹ r r := by
    simp [inverseMatrixPair,Pi.single_apply]
  have hl (r : ι) : inverseMatrixPair A (fun _ => 1) (Pi.single r 1) = ∑ j, A⁻¹ r j := by
    simp [inverseMatrixPair,Pi.single_apply]
  have hr (r : ι) : inverseMatrixPair A (Pi.single r 1) (fun _ => 1) = ∑ i, A⁻¹ i r := by
    simp [inverseMatrixPair,Pi.single_apply]
  have hone : inverseMatrixPair A (fun _ => 1) (fun _ => 1) = ∑ j, ∑ i, A⁻¹ i j := by
    simp [inverseMatrixPair]
  have hx (r : ι) : inverseMatrixPair A (capTiltedCovector r) (capTiltedCovector r) =
      inverseMatrixPair A (fun _ => 1) (fun _ => 1) + (∑ j, A⁻¹ r j) +
        ((∑ i, A⁻¹ i r) + A⁻¹ r r) := by
    change inverseMatrixPair A (fun i => (fun _ : ι => (1:ℝ)) i + (Pi.single r 1 : ι → ℝ) i)
      (fun i => (fun _ : ι => (1:ℝ)) i + (Pi.single r 1 : ι → ℝ) i) = _
    rw [inverseMatrixPair_add_left A (fun _ => 1) (Pi.single r 1),
      inverseMatrixPair_add_right A (fun _ => 1) (fun _ => 1) (Pi.single r 1),
      inverseMatrixPair_add_right A (Pi.single r 1) (fun _ => 1) (Pi.single r 1),hl,hr,hd]
  simp_rw [hx]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [show (∑ r, ∑ j, A⁻¹ r j) = ∑ j, ∑ i, A⁻¹ i j by rw [Finset.sum_comm],← hone]
  change _ = (∑ i, A⁻¹ i i)+_
  ring

/- The literal trace of the inverse Hessian is controlled by the finite
family of tilted cap energies, with sharp coefficient one. -/
lemma inverse_trace_le_tilted {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    A⁻¹.trace ≤ ∑ r, inverseMatrixPair A (capTiltedCovector r) (capTiltedCovector r) := by
  rw [inverse_trace_tilted_identity]
  exact le_add_of_nonneg_right (mul_nonneg (by positivity)
    (inverseMatrixPair_self_nonneg hA _))

lemma inverse_trace_nonneg {A : Matrix ι ι ℝ} (hA : A.PosDef) : 0 ≤ A⁻¹.trace := by
  exact Finset.sum_nonneg (fun i _ => hA.inv.posSemidef.diag_nonneg (i := i))

/- Integration of the preceding finite-family estimate. This closes the
last purely algebraic summation step after actual cap transport. -/
theorem integral_inverse_trace_le_cap_sum {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {B : α → Matrix ι ι ℝ} {I : α → ℝ}
    (hB : ∀ᵐ x ∂μ, (B x).PosDef) (hI : 0 ≤ᵐ[μ] I)
    (hi : Integrable (fun x => I x*(B x)⁻¹.trace) μ)
    (hc : ∀ r, Integrable (fun x => I x*inverseMatrixPair (B x)
      (capTiltedCovector r) (capTiltedCovector r)) μ) :
    (∫ x, I x*(B x)⁻¹.trace ∂μ) ≤ ∑ r, ∫ x, I x*inverseMatrixPair (B x)
      (capTiltedCovector r) (capTiltedCovector r) ∂μ := by
  rw [← integral_finsetSum _ (fun index _ => hc index)]
  apply integral_mono_ae hi (integrable_finsetSum _ (fun index _ => hc index))
  filter_upwards [hB,hI] with x hx hIx
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (inverse_trace_le_tilted hx) hIx

end AffineBernstein
end

end OAI

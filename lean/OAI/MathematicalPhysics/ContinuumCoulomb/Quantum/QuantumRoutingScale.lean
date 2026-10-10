import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingSpectrum

namespace OAI

/-! A polynomial penalty choice for the second-order routing gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Kronecker

def qmaRoutingScale (A B N : ℝ) : ℝ := 16*(A+B+1)^3*N+4*(A+B+1)+1

theorem qmaRoutingScale_bounds {A B N : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 < N) :
    let R := qmaRoutingScale A B N
    0 < R ∧ 0 ≤ (A+B+1)/R ∧ (A+B+1)/R ≤ 1/4 ∧
      B+A*R ≤ ((A+B+1)/R)*(4*R^2) ∧
      16*R^2*((A+B+1)/R)^3 ≤ 1/N := by
  let Q := A+B+1
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hq3 : 0 ≤ 16*Q^3*N := by positivity
  have hR : 0 < qmaRoutingScale A B N := by
    change 0 < 16*Q^3*N+4*Q+1
    positivity
  have hR1 : 1 ≤ qmaRoutingScale A B N := by
    change 1 ≤ 16*Q^3*N+4*Q+1
    nlinarith
  have hR4 : 4*Q ≤ qmaRoutingScale A B N := by
    change 4*Q ≤ 16*Q^3*N+4*Q+1
    linarith
  have hR16 : 16*Q^3*N ≤ qmaRoutingScale A B N := by
    change 16*Q^3*N ≤ 16*Q^3*N+4*Q+1
    linarith
  refine ⟨hR,div_nonneg hQ.le hR.le,?_,?_,?_⟩
  · apply (div_le_iff₀ hR).mpr
    change Q ≤ (1/4)*qmaRoutingScale A B N
    linarith
  · have heq : (Q/qmaRoutingScale A B N)*(4*qmaRoutingScale A B N^2) =
        4*Q*qmaRoutingScale A B N := by field_simp
    change B+A*qmaRoutingScale A B N ≤ (Q/qmaRoutingScale A B N)*(4*qmaRoutingScale A B N^2)
    rw [heq]
    have hbR := mul_le_mul_of_nonneg_left hR1 hB
    have hqR := mul_nonneg hQ.le hR.le
    dsimp [Q] at *
    nlinarith
  · change 16*qmaRoutingScale A B N^2*(Q/qmaRoutingScale A B N)^3 ≤ 1/N
    have heq : 16*qmaRoutingScale A B N^2*(Q/qmaRoutingScale A B N)^3 =
        16*Q^3/qmaRoutingScale A B N := by field_simp
    rw [heq]
    apply (div_le_iff₀ hR).mpr
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using (le_div_iff₀ hN).mpr hR16

theorem qmaRouting_accuracy (n r : ℕ) {A B N : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hN : 0 < N)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (W : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)
    (hW : W.conjTranspose = W) (hWlow : mediatorCompression n r W = 0)
    (hCn : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ B)
    (hWn : ‖spinMatrixOperator W‖ ≤ A*qmaRoutingScale A B N) :
    let R := qmaRoutingScale A B N
    |mediatorFullBottom n r (routingHamiltonian n r (R^2) C W) -
      sourceMatrixBottom n (C - mediatorCompression n r
        (W * liftedMediatorInverse n r (R^2) * W))| ≤ 1/N := by
  obtain ⟨hR,he,hes,hb,ha⟩ := qmaRoutingScale_bounds hA hB hN
  exact (routing_bottom n r (sq_pos_of_pos hR) C hC W hW hWlow he hes
    ((add_le_add hCn hWn).trans hb)).trans ha

end ContinuumCoulomb

end

end OAI

import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGadgetAlgebra

namespace OAI

/-! Exact counterterms make the subdivision and three-body Schur
complements equal the intended interactions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaSubdivisionCoupling (A B : Matrix ι ι ℂ) (r J : ℂ) : Matrix ι ι ℂ :=
  r • (A+(-J/2) • B)

def qmaSubdivisionCounter (rJ : ℂ) : Matrix ι ι ℂ :=
  (1+(-rJ/2)^2) • (1 : Matrix ι ι ℂ)

theorem qmaSubdivision_effective (A B : Matrix ι ι ℂ) (r J : ℂ) (hr : r ≠ 0)
    (hA : A*A = 1) (hB : B*B = 1) (hAB : A*B = B*A) :
    qmaSubdivisionCounter J-
      qmaSubdivisionCoupling A B r J*((r^2)⁻¹ • (1 : Matrix ι ι ℂ))*
        qmaSubdivisionCoupling A B r J = J • (A*B) := by
  unfold qmaSubdivisionCounter qmaSubdivisionCoupling
  have hs : r * (r^2)⁻¹ * r = 1 := by field_simp
  have hp : (r • (A+(-J/2) • B))*((r^2)⁻¹ • (1 : Matrix ι ι ℂ))*
      (r • (A+(-J/2) • B)) = (A+(-J/2) • B)*(A+(-J/2) • B) := by
    simp only [smul_mul_assoc, mul_smul_comm, mul_one, smul_smul]
    rw [← mul_assoc, hs, one_smul]
  rw [hp, qmaGadget_pair_square A B (-J/2) hA hB hAB]
  module

def qmaThirdGadgetWeight (r J : ℂ) : ℂ := J*((r^3)^2-(r^2)^2)/(2*r^6)

def qmaThirdGadgetCoupling (A B : Matrix ι ι ℂ) (r J : ℂ) : Matrix ι ι ℂ :=
  r^2 • (A+qmaThirdGadgetWeight r J • B)

def qmaThirdGadgetCounter (A B C : Matrix ι ι ℂ) (r J : ℂ) : Matrix ι ι ℂ :=
  let c := qmaThirdGadgetWeight r J
  ((r^2*r^2)*((r^3)^2-(r^2)^2)⁻¹) •
    (r^3 • ((1+c^2) • (1 : Matrix ι ι ℂ)+(2*c) • (A*B))-
      r^2 • ((1+c^2) • C))

theorem qmaThirdGadget_effective (A B C : Matrix ι ι ℂ) (r J : ℂ)
    (hr : r ≠ 0) (hden : (r^3)^2-(r^2)^2 ≠ 0)
    (hA : A*A = 1) (hB : B*B = 1) (hAB : A*B = B*A)
    (hAC : A*C = C*A) (hBC : B*C = C*B) :
    qmaThirdGadgetCounter A B C r J-
      qmaThirdGadgetCoupling A B r J*qmaGadgetPenaltyInverse C (r^3) (r^2)*
        qmaThirdGadgetCoupling A B r J = J • (A*B*C) := by
  have he : qmaThirdGadgetCounter A B C r J-
      qmaThirdGadgetCoupling A B r J*qmaGadgetPenaltyInverse C (r^3) (r^2)*
        qmaThirdGadgetCoupling A B r J =
      ((r^2*r^2)*((r^3)^2-(r^2)^2)⁻¹*r^2*(2*qmaThirdGadgetWeight r J)) • (A*B*C) := by
    unfold qmaThirdGadgetCounter qmaThirdGadgetCoupling
    rw [smul_mul_assoc,mul_smul_comm,smul_mul_assoc,smul_smul,
      qmaGadget_effective A B C (r^3) (r^2) (qmaThirdGadgetWeight r J) hA hB hAB hAC hBC]
    module
  rw [he]
  have hc : (r^2*r^2)*((r^3)^2-(r^2)^2)⁻¹*r^2*(2*qmaThirdGadgetWeight r J) = J := by
    unfold qmaThirdGadgetWeight
    have h2 : r^2-1 ≠ 0 := by
      intro h
      apply hden
      calc
        _ = r^4*(r^2-1) := by ring
        _ = 0 := by rw [h, mul_zero]
    field_simp [hr, hden, h2]
  rw [hc]

end ContinuumCoulomb

end

end OAI

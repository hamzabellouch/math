import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGadgetCounterterms

namespace OAI

/-! The third-order series gadget uses only polynomial coefficients.
Its parallel version is controlled by ThirdOrderPerturbation. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaThirdSeriesPair (A B : Matrix ι ι ℂ) (J : ℂ) : Matrix ι ι ℂ :=
  A+(J/2) • B

def qmaThirdSeriesCounter (A B C : Matrix ι ι ℂ) (r J : ℂ) : Matrix ι ι ℂ :=
  r • ((1+(J/2)^2) • (1 : Matrix ι ι ℂ)+J • (A*B))-
    (1+(J/2)^2) • C

theorem qmaThirdSeries_effective (A B C : Matrix ι ι ℂ) (r J : ℂ)
    (hA : A*A = 1) (hB : B*B = 1) (hAB : A*B = B*A)
    (hAC : A*C = C*A) (hBC : B*C = C*B) :
    qmaThirdSeriesCounter A B C r J -
      r • (qmaThirdSeriesPair A B J*qmaThirdSeriesPair A B J)+
      qmaThirdSeriesPair A B J*C*qmaThirdSeriesPair A B J = J • (A*B*C) := by
  unfold qmaThirdSeriesCounter qmaThirdSeriesPair
  rw [qmaGadget_pair_square A B (J/2) hA hB hAB,
    qmaGadget_pair_sandwich A B C (J/2) hA hB hAB hAC hBC]
  module

theorem qmaThirdSeries_scaled_effective (A B C : Matrix ι ι ℂ) (r J : ℂ)
    (hr : r ≠ 0) (hA : A*A = 1) (hB : B*B = 1) (hAB : A*B = B*A)
    (hAC : A*C = C*A) (hBC : B*C = C*B) :
    qmaThirdSeriesCounter A B C r J -
      (r^3)⁻¹ • ((r^2 • qmaThirdSeriesPair A B J)*(r^2 • qmaThirdSeriesPair A B J))+
      ((r^3)⁻¹ • (r^2 • qmaThirdSeriesPair A B J))*(r^2 • C)*
        ((r^3)⁻¹ • (r^2 • qmaThirdSeriesPair A B J)) = J • (A*B*C) := by
  have hfirst : (r^3)⁻¹*(r^2*r^2) = r := by field_simp
  have hthird : ((r^3)⁻¹*r^2)*r^2*((r^3)⁻¹*r^2) = 1 := by field_simp
  simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
  rw [hfirst]
  have ht : ((r^3)⁻¹*r^2)*(r^2*((r^3)⁻¹*r^2)) = 1 := by
    rw [← mul_assoc]
    exact hthird
  rw [ht,one_smul]
  exact qmaThirdSeries_effective A B C r J hA hB hAB hAC hBC

end ContinuumCoulomb

end

end OAI

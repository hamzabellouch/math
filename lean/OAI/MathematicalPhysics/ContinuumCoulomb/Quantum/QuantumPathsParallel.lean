import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathSpectrum
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumParallelGraph

namespace OAI

/-! A whole layer of independently even or odd path subdivisions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaPaths_effective {n r : ℕ} (site : Fin r → Fin 2 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (even : Fin r → Bool)
    (R : ℝ) (hR : R ≠ 0) (J : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    (C + ∑ e, qmaPathCorrection (n := n) R (J e)) -
      mediatorCompression n r (qmaRoutingStars n r site (fun e => qmaPathMember (even e))
          (fun e => qmaPathAmplitude (even e) R (J e)) * liftedMediatorInverse n r (R^2) *
        qmaRoutingStars n r site (fun e => qmaPathMember (even e))
          (fun e => qmaPathAmplitude (even e) R (J e))) =
      C + ∑ e, (J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) := by
  rw [qmaRoutingStars_compression,add_sub_assoc,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact qmaPathSubdivision_effective e (site e) (hsite e) (even e) R (J e) hR

theorem qmaPaths_bottom {n r : ℕ} (site : Fin r → Fin 2 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (even : Fin r → Bool)
    (R : ℝ) (hR : 0 < R) (J : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1/4)
    (hbound : ‖spinMatrixOperator ((C + ∑ e, qmaPathCorrection (n := n) R (J e)) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |qmaPathAmplitude (even e) R (J e) a| ≤ epsilon*(4*R^2)) :
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + ∑ e, qmaPathCorrection (n := n) R (J e))
        (qmaRoutingStars n r site (fun e => qmaPathMember (even e))
          (fun e => qmaPathAmplitude (even e) R (J e)))) -
      sourceMatrixBottom n (C + ∑ e,
        (J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1))| ≤ 16*R^2*epsilon^3 := by
  have hCW : (C + ∑ e, qmaPathCorrection (n := n) R (J e)).conjTranspose =
      C + ∑ e, qmaPathCorrection (n := n) R (J e) := by
    simp only [qmaPathCorrection,Matrix.conjTranspose_add,Matrix.conjTranspose_sum,hC,
      Matrix.conjTranspose_smul,Matrix.conjTranspose_one,Complex.star_def,Complex.conj_ofReal]
  have h := qmaRoutingStars_bottom n r (sq_pos_of_pos hR) _ hCW site
    (fun e => qmaPathMember (even e)) (fun e => qmaPathAmplitude (even e) R (J e))
    hepsilon hsmall hbound
  rw [qmaPaths_effective site hsite even R hR.ne' J C] at h
  exact h

theorem qmaPathAmplitude_norm (even : Bool) (R J : ℝ) (hR : 0 ≤ R) :
    3*(∑ a, |qmaPathAmplitude even R J a|) = 3*R*(1+2*|J|) := by
  cases even <;> simp [qmaPathAmplitude,Fin.sum_univ_succ,abs_mul,abs_of_nonneg hR] <;> ring

theorem qmaPathCorrection_lift_norm (n r : ℕ) (R J : ℝ) :
    ‖spinMatrixOperator (qmaPathCorrection (n := n) R J ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ 4*(1+|J|)^2 := by
  have hI : ‖spinMatrixOperator (1 : Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ)‖ ≤ 1 := by
    apply spinMatrixOperator_unitary_norm
    simp
  rw [qmaPathCorrection,Matrix.smul_kronecker,Matrix.one_kronecker_one,spinMatrixOperator_smul,
    norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have hoff : 0 ≤ 3/4+3*J^2 := by positivity
  rw [abs_of_nonneg hoff]
  calc
    _ ≤ (3/4+3*J^2)*1 := mul_le_mul_of_nonneg_left hI hoff
    _ ≤ _ := by nlinarith [sq_abs J,abs_nonneg J]

end ContinuumCoulomb

end

end OAI

import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkParallel
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingScale

namespace OAI

/-! Explicit polynomial calibration for a simultaneous fork stage. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaForks_correction_norm {n r : ℕ} (site : Fin r → Fin 3 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (J K : Fin r → ℝ) :
    ‖spinMatrixOperator ((∑ e, qmaForkCorrection (site e) (J e) (K e)) ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤
      12*∑ e, (1+|J e|+|K e|)^2 := by
  rw [MediatorGraph.sum_kronecker,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ =>
    qmaForkCorrection_lift_norm (site e) (hsite e) (J e) (K e)))

theorem qmaForks_amplitude (r : ℕ) (R : ℝ) (hR : 0 ≤ R) (J K : Fin r → ℝ) :
    3*(∑ e, ∑ a, |qmaForkAmplitude R (J e) (K e) a|) =
      (3*∑ e, (1+2*|J e|+2*|K e|))*R := by
  rw [Finset.mul_sum]
  simp_rw [qmaForkAmplitude_norm R _ _ hR]
  rw [← Finset.mul_sum]
  ring

theorem qmaForks_accuracy {n r : ℕ} (site : Fin r → Fin 3 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (J K : Fin r → ℝ)
    {B N : ℝ} (hB : 0 ≤ B) (hN : 0 < N)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (hCn : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ B) :
    let A := 3*∑ e, (1+2*|J e|+2*|K e|)
    let D := B+12*∑ e, (1+|J e|+|K e|)^2
    let R := qmaRoutingScale A D N
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + ∑ e, qmaForkCorrection (site e) (J e) (K e))
        (qmaRoutingStars n r site (fun _ => qmaForkMember)
          (fun e => qmaForkAmplitude R (J e) (K e)))) -
      sourceMatrixBottom n (C + ∑ e,
        ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2)))| ≤ 1/N := by
  let A := 3*∑ e, (1+2*|J e|+2*|K e|)
  let D := B+12*∑ e, (1+|J e|+|K e|)^2
  let R := qmaRoutingScale A D N
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨hR,he,hes,hbound,herr⟩ := qmaRoutingScale_bounds hA hD hN
  have hCC : ‖spinMatrixOperator ((C + ∑ e, qmaForkCorrection (site e) (J e) (K e)) ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ D := by
    rw [Matrix.add_kronecker,spinMatrixOperator_add]
    exact (norm_add_le _ _).trans (add_le_add hCn (qmaForks_correction_norm site hsite J K))
  have hb : ‖spinMatrixOperator ((C + ∑ e, qmaForkCorrection (site e) (J e) (K e)) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |qmaForkAmplitude R (J e) (K e) a| ≤ ((A+D+1)/R)*(4*R^2) := by
    rw [qmaForks_amplitude r R hR.le J K]
    exact (add_le_add hCC (le_refl (A*R))).trans hbound
  exact (qmaForks_bottom site hsite R hR J K C hC he hes hb).trans herr

end ContinuumCoulomb

end

end OAI

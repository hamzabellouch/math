import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathsParallel

namespace OAI

/-! Polynomial penalty for a simultaneous layer of arbitrary parity subdivisions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaPaths_correction_norm (n r : ℕ) (R : ℝ) (J : Fin r → ℝ) :
    ‖spinMatrixOperator ((∑ e, qmaPathCorrection (n := n) R (J e)) ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤
      4*∑ e, (1+|J e|)^2 := by
  rw [MediatorGraph.sum_kronecker,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ =>
    qmaPathCorrection_lift_norm n r R (J e)))

theorem qmaPaths_amplitude (r : ℕ) (even : Fin r → Bool) (R : ℝ) (hR : 0 ≤ R) (J : Fin r → ℝ) :
    3*(∑ e, ∑ a, |qmaPathAmplitude (even e) R (J e) a|) =
      (3*∑ e, (1+2*|J e|))*R := by
  rw [Finset.mul_sum]
  simp_rw [qmaPathAmplitude_norm _ R _ hR]
  rw [← Finset.mul_sum]
  ring

theorem qmaPaths_accuracy {n r : ℕ} (site : Fin r → Fin 2 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (even : Fin r → Bool) (J : Fin r → ℝ)
    {B N : ℝ} (hB : 0 ≤ B) (hN : 0 < N)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    (hCn : ‖spinMatrixOperator (C ⊗ₖ (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ B) :
    let A := 3*∑ e, (1+2*|J e|)
    let D := B+4*∑ e, (1+|J e|)^2
    let R := qmaRoutingScale A D N
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + ∑ e, qmaPathCorrection (n := n) R (J e))
        (qmaRoutingStars n r site (fun e => qmaPathMember (even e))
          (fun e => qmaPathAmplitude (even e) R (J e)))) -
      sourceMatrixBottom n (C + ∑ e,
        (J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1))| ≤ 1/N := by
  let A := 3*∑ e, (1+2*|J e|)
  let D := B+4*∑ e, (1+|J e|)^2
  let R := qmaRoutingScale A D N
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨hR,he,hes,hbound,herr⟩ := qmaRoutingScale_bounds hA hD hN
  have hCC : ‖spinMatrixOperator ((C + ∑ e, qmaPathCorrection (n := n) R (J e)) ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ D := by
    rw [Matrix.add_kronecker,spinMatrixOperator_add]
    exact (norm_add_le _ _).trans (add_le_add hCn (qmaPaths_correction_norm n r R J))
  have hb : ‖spinMatrixOperator ((C + ∑ e, qmaPathCorrection (n := n) R (J e)) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |qmaPathAmplitude (even e) R (J e) a| ≤ ((A+D+1)/R)*(4*R^2) := by
    rw [qmaPaths_amplitude r even R hR.le J]
    exact (add_le_add hCC (le_refl (A*R))).trans hbound
  exact (qmaPaths_bottom site hsite even R hR J C hC he hes hb).trans herr

end ContinuumCoulomb

end

end OAI

import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkSpectrum

namespace OAI

/-! Simultaneous fork elimination, with no mixed error between distinct singlets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaForks_effective {n r : ℕ} (site : Fin r → Fin 3 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (R : ℝ) (hR : R ≠ 0) (J K : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    (C + ∑ e, qmaForkCorrection (site e) (J e) (K e)) -
      mediatorCompression n r (qmaRoutingStars n r site (fun _ => qmaForkMember)
          (fun e => qmaForkAmplitude R (J e) (K e)) * liftedMediatorInverse n r (R^2) *
        qmaRoutingStars n r site (fun _ => qmaForkMember)
          (fun e => qmaForkAmplitude R (J e) (K e))) =
      C + ∑ e, ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) +
        (K e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2)) := by
  rw [qmaRoutingStars_compression,add_sub_assoc,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact qmaFork_effective e (site e) (hsite e) R (J e) (K e) hR

theorem qmaForks_bottom {n r : ℕ} (site : Fin r → Fin 3 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (R : ℝ) (hR : 0 < R) (J K : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1/4)
    (hbound : ‖spinMatrixOperator ((C + ∑ e, qmaForkCorrection (site e) (J e) (K e)) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |qmaForkAmplitude R (J e) (K e) a| ≤ epsilon * (4*R^2)) :
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + ∑ e, qmaForkCorrection (site e) (J e) (K e))
        (qmaRoutingStars n r site (fun _ => qmaForkMember)
          (fun e => qmaForkAmplitude R (J e) (K e)))) -
      sourceMatrixBottom n (C + ∑ e,
        ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 1) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2)))| ≤
      16*R^2*epsilon^3 := by
  have hCW : (C + ∑ e, qmaForkCorrection (site e) (J e) (K e)).conjTranspose =
      C + ∑ e, qmaForkCorrection (site e) (J e) (K e) := by
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_sum,hC,
      qmaForkCorrection_star _ (hsite _)]
  have h := qmaRoutingStars_bottom n r (sq_pos_of_pos hR) _ hCW site
    (fun _ => qmaForkMember) (fun e => qmaForkAmplitude R (J e) (K e))
    hepsilon hsmall hbound
  rw [qmaForks_effective site hsite R hR.ne' J K C] at h
  exact h

end ContinuumCoulomb

end

end OAI

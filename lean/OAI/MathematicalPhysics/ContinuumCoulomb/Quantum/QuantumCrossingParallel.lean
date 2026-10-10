import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSpectrum

namespace OAI

/-! Simultaneous crossing elimination, with no mixed error between distinct singlets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

theorem qmaCrossings_effective {n r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (R : ℝ) (hR : R ≠ 0) (J K : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) :
    (C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e)) -
      mediatorCompression n r (qmaRoutingStars n r site (fun _ => qmaCrossingMember)
          (fun e => qmaCrossingAmplitude R (J e) (K e)) * liftedMediatorInverse n r (R^2) *
        qmaRoutingStars n r site (fun _ => qmaCrossingMember)
          (fun e => qmaCrossingAmplitude R (J e) (K e))) =
      C + ∑ e, ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2) +
        (K e:ℂ) • sourceHeisenbergMatrix n (site e 1) (site e 3)) := by
  rw [qmaRoutingStars_compression,add_sub_assoc,← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  exact qmaCrossing_effective e (site e) (hsite e) R (J e) (K e) hR

theorem qmaCrossings_bottom {n r : ℕ} (site : Fin r → Fin 4 → Fin n)
    (hsite : ∀ e, Function.Injective (site e)) (R : ℝ) (hR : 0 < R) (J K : Fin r → ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1/4)
    (hbound : ‖spinMatrixOperator ((C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e)) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ e, ∑ a, |qmaCrossingAmplitude R (J e) (K e) a| ≤ epsilon * (4*R^2)) :
    |mediatorFullBottom n r (routingHamiltonian n r (R^2)
        (C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e))
        (qmaRoutingStars n r site (fun _ => qmaCrossingMember)
          (fun e => qmaCrossingAmplitude R (J e) (K e)))) -
      sourceMatrixBottom n (C + ∑ e,
        ((J e:ℂ) • sourceHeisenbergMatrix n (site e 0) (site e 2) +
          (K e:ℂ) • sourceHeisenbergMatrix n (site e 1) (site e 3)))| ≤
      16*R^2*epsilon^3 := by
  have hCW : (C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e)).conjTranspose =
      C + ∑ e, qmaCrossingCorrection (site e) (J e) (K e) := by
    simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_sum,hC,
      qmaCrossingCorrection_star _ (hsite _)]
  have h := qmaRoutingStars_bottom n r (sq_pos_of_pos hR) _ hCW site
    (fun _ => qmaCrossingMember) (fun e => qmaCrossingAmplitude R (J e) (K e))
    hepsilon hsmall hbound
  rw [qmaCrossings_effective site hsite R hR.ne' J K C] at h
  exact h

end ContinuumCoulomb

end

end OAI

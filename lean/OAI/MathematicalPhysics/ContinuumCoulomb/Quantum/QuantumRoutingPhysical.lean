import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingSpectrum
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorPhysical

namespace OAI

/-! Actual physical spin interactions for the singlet routing construction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker InnerProductSpace
variable {κ : Type*} [Fintype κ]

def qmaPhysicalSingletStar (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  ∑ a, (amplitude a:ℂ) • ∑ μ : Fin 3,
    sourceLocalPauli n (site a) μ ⊗ₖ mediatorLocal r e (physicalMemberPauli (member a) μ)

theorem qmaPhysicalSingletStar_transform (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      qmaPhysicalSingletStar n r e site member amplitude * fullMediatorBellMatrix n r =
      qmaSingletStar n r e site member amplitude := by
  simp only [qmaPhysicalSingletStar,qmaSingletStar,mediatorAxisSpoke,
    Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,physicalSpoke_bellTransform]

def qmaPhysicalRoutingHamiltonian (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (e : Fin r) (site : κ → Fin n) (member : κ → Fin 2) (amplitude : κ → ℝ) :
    Matrix (MediatedSpinBasis n r) (MediatedSpinBasis n r) ℂ :=
  1 ⊗ₖ physicalMediatorPenalty r Delta +
    (C ⊗ₖ 1 + qmaPhysicalSingletStar n r e site member amplitude)

theorem qmaPhysicalRoutingHamiltonian_transform (n r : ℕ) (Delta : ℝ)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ)
    (e : Fin r) (site : κ → Fin n) (member : κ → Fin 2) (amplitude : κ → ℝ) :
    (fullMediatorBellMatrix n r).conjTranspose *
      qmaPhysicalRoutingHamiltonian n r Delta C e site member amplitude *
        fullMediatorBellMatrix n r =
      routingHamiltonian n r Delta C (qmaSingletStar n r e site member amplitude) := by
  simp only [qmaPhysicalRoutingHamiltonian,routingHamiltonian,mul_add,add_mul,
    physicalMediatorPenalty_full_transform,liftedSource_full_transform,qmaPhysicalSingletStar_transform]

theorem qmaPhysicalCrossing_bottom {n r : ℕ} (e : Fin r) (site : Fin 4 → Fin n)
    (hsite : Function.Injective site) (R J K : ℝ) (hR : 0 < R)
    (C : Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ) (hC : C.conjTranspose = C)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hsmall : epsilon ≤ 1 / 4)
    (hbound : ‖spinMatrixOperator ((C + qmaCrossingCorrection site J K) ⊗ₖ
        (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ +
      3*∑ a, |qmaCrossingAmplitude R J K a| ≤ epsilon * (4 * R^2)) :
    |mediatorFullBottom n r (qmaPhysicalRoutingHamiltonian n r (R^2)
        (C + qmaCrossingCorrection site J K) e site qmaCrossingMember
        (qmaCrossingAmplitude R J K)) -
      sourceMatrixBottom n (C + ((J:ℂ) • sourceHeisenbergMatrix n (site 0) (site 2) +
        (K:ℂ) • sourceHeisenbergMatrix n (site 1) (site 3)))| ≤ 16 * R^2 * epsilon^3 := by
  have hb := mediatorFullBottom_unitary n r (fullMediatorBellMatrix n r)
    (qmaPhysicalRoutingHamiltonian n r (R^2) (C + qmaCrossingCorrection site J K)
      e site qmaCrossingMember (qmaCrossingAmplitude R J K))
    (fullMediatorBellMatrix_gram n r) (fullMediatorBellMatrix_cogram n r)
  rw [qmaPhysicalRoutingHamiltonian_transform] at hb
  rw [← hb]
  exact qmaCrossing_bottom e site hsite R J K hR C hC hepsilon hsmall hbound

end ContinuumCoulomb

end

end OAI

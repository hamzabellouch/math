import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationAction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPolynomialOperations
import Mathlib.GroupTheory.SemidirectProduct

namespace OAI

/-! # Analytic semidirect products for the nilpotent induction

The carrier is the vector space `L × ℝ`. Its operations are polynomial because
the action is the exponential of a nilpotent derivation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

def derivationSemidirectEquiv : (L × ℝ) ≃
    (L ⋊[PolynomialExponentialCoordinates.derivationAction D hD] Multiplicative ℝ) where
  toFun p := ⟨p.1, Multiplicative.ofAdd p.2⟩
  invFun p := (p.left, p.right.toAdd)
  left_inv _ := rfl
  right_inv _ := rfl

@[instance_reducible] def derivationSemidirectGroup : Group (L × ℝ) :=
  (derivationSemidirectEquiv D hD).group

section Operations

theorem derivationSemidirect_mul (x y : L × ℝ) :
    (derivationSemidirectGroup D hD).mul x y =
      (x.1 * nilpotentDerivationFlow D hD x.2 y.1, x.2 + y.2) := rfl

theorem derivationSemidirect_one :
    (derivationSemidirectGroup D hD).one = (0, 0) := by
  change ((1 : L), (0 : ℝ)) = (0, 0)
  rw [P.one_eq_zero]

theorem derivationSemidirect_inv (x : L × ℝ) :
    (derivationSemidirectGroup D hD).inv x =
      (nilpotentDerivationFlow D hD (-x.2) (-x.1), -x.2) := by
  change (nilpotentDerivationFlow D hD (-x.2) (x.1⁻¹), -x.2) = _
  rw [P.inv_eq_neg]

theorem contDiff_derivationSemidirect_mul {r : ℕ∞ω} :
    ContDiff ℝ r (fun p : (L × ℝ) × (L × ℝ) =>
      (finiteDynkinPolynomial P.coefficients
        ![p.1.1, nilpotentDerivationFlow D hD p.1.2 p.2.1], p.1.2 + p.2.2)) := by
  have hflow : ContDiff ℝ r (fun p : (L × ℝ) × (L × ℝ) =>
      nilpotentDerivationFlow D hD p.1.2 p.2.1) :=
    contDiff_derivationFlow_comp D hD (contDiff_fst.snd) (contDiff_snd.fst)
  have hpoly : ContDiff ℝ r (fun p : (L × ℝ) × (L × ℝ) =>
      finiteDynkinPolynomial P.coefficients ![p.1.1, nilpotentDerivationFlow D hD p.1.2 p.2.1]) := by
    exact contDiff_binaryDynkin_comp P.coefficients (contDiff_fst.fst) hflow
  exact hpoly.prodMk ((contDiff_fst.snd).add (contDiff_snd.snd))

omit P in
theorem contDiff_derivationSemidirect_inv {r : ℕ∞ω} :
    ContDiff ℝ r (fun p : L × ℝ =>
      (nilpotentDerivationFlow D hD (-p.2) (-p.1), -p.2)) := by
  exact (contDiff_derivationFlow_comp D hD contDiff_snd.neg contDiff_fst.neg).prodMk
    contDiff_snd.neg

theorem derivationSemidirectLieGroup :
    letI := derivationSemidirectGroup D hD
    LieGroup (𝓘(ℝ, L × ℝ)) ⊤ (L × ℝ) := by
  let := derivationSemidirectGroup D hD
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · have heq : (fun p : (L × ℝ) × (L × ℝ) => (derivationSemidirectGroup D hD).mul p.1 p.2) =
        (fun p => (finiteDynkinPolynomial P.coefficients
          ![p.1.1, nilpotentDerivationFlow D hD p.1.2 p.2.1], p.1.2 + p.2.2)) := by
      funext p
      rw [derivationSemidirect_mul, P.mul_eq]
    change ContMDiff _ _ _ (fun p : (L × ℝ) × (L × ℝ) =>
      (derivationSemidirectGroup D hD).mul p.1 p.2)
    rw [heq]
    exact (contDiff_derivationSemidirect_mul D hD).comp_contMDiff
      (contMDiff_fst.prodMk_space contMDiff_snd)
  · have heq : (fun p : L × ℝ => (derivationSemidirectGroup D hD).inv p) =
        (fun p => (nilpotentDerivationFlow D hD (-p.2) (-p.1), -p.2)) :=
      funext (derivationSemidirect_inv D hD)
    change ContMDiff _ _ _ (fun p : L × ℝ => (derivationSemidirectGroup D hD).inv p)
    rw [heq]
    exact (contDiff_derivationSemidirect_inv D hD).contMDiff

end Operations
end PolycyclicRecognition

end

end OAI

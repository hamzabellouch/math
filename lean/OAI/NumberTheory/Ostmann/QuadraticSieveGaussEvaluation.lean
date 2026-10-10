import OAI.NumberTheory.Ostmann.QuadraticSieveGauss
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussBridge
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussEvaluationNormalization

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Complex
open scoped BigOperators

theorem quadratic_gauss_sum_evaluation (q : ℕ) [NeZero q] (hq : Odd q) :
    (∑ a : ZMod q, ZMod.stdAddChar (a^2)) =
      (if q%4=1 then (1 : ℂ) else I)*(Real.sqrt (q : ℝ) : ℂ) := by
  rw [←sum_fin_residues_eq_sum_zmod q (fun a => ZMod.stdAddChar (a^2))]
  change (∑ a : Fin q, quadraticResidueWeight q a)=_
  rw [quadratic_phase_sum_identity]
  have hmod : q%4=1 ∨ q%4=3 := by
    have h := Nat.odd_iff.mp hq
    omega
  rcases hmod with h|h
  · rw [inverseResidueWeight_sum_one h,ite_eq_left h]
    ring_nf
    simp only [I_sq]
    ring
  · rw [inverseResidueWeight_sum_three h,ite_eq_right (by omega)]
    ring_nf
    simp only [I_sq]
    ring

theorem jacobi_gauss_evaluation {q : ℕ} [NeZero q] (hq : Odd q) (hsq : Squarefree q) :
    gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar =
      (if q%4=1 then (1 : ℂ) else I)*(Real.sqrt (q : ℝ) : ℂ) := by
  rw [←quadratic_sum_eq_jacobi_gauss hq hsq]
  exact quadratic_gauss_sum_evaluation q hq

end Ostmann.QuadraticSieve

end

end OAI

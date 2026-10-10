import OAI.Combinatorics.PolynomialVacuum.Algebra.PrescriptionCollision
import OAI.Combinatorics.PolynomialVacuum.Algebra.CandidateEndpoints

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

 
theorem eval_reinsertLast {m : ℕ} (p : Polynomial (MvPolynomial (Fin m) ℂ))
    (Z : Fin (m+1) → ℂ) :
    eval Z (reinsertLast p)=p.eval₂ (eval (Z ∘ Fin.castSucc)) (T⁻¹*Z (Fin.last m)) := by
  unfold reinsertLast
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [Polynomial.eval₂_add,map_add,hp,hr]
  | monomial k a => simp [Polynomial.eval₂_monomial,eval_rename]

theorem eval_reinsertLast_node {m : ℕ} (p : Polynomial (MvPolynomial (Fin m) ℂ))
    (Z : Fin (m+1) → ℂ) (i : Fin m) (hZ : Z (Fin.last m)=T*Z i.castSucc) :
    eval Z (reinsertLast p)=eval (Z ∘ Fin.castSucc) (p.eval (X i)) := by
  rw [eval_reinsertLast]
  have hx : T⁻¹*Z (Fin.last m)=eval (Z ∘ Fin.castSucc) (X i) := by
    simp [hZ,T_ne_zero,Function.comp_apply]
  rw [hx,Polynomial.eval₂_at_apply]

 

theorem interpolateState_node {n : ℕ} (ψ : State n) (χ : State (n+1))
    (hψ : LowerExchange (liftState ψ) n) (s : Fin (n+2) → Spin)
    (Z : Fin (n+2) → ℂ) (i : Fin (n+1))
    (hZ : Z (Fin.last (n+1))=T*Z i.castSucc) :
    eval Z (interpolateState ψ χ s)=eval (Z ∘ Fin.castSucc) (cupPrescription ψ i s) := by
  have hzero : (∏ j : Fin (n+1), (Z j.castSucc-T⁻¹*Z (Fin.last (n+1))))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hZ,T_ne_zero]
  unfold interpolateState
  split_ifs with hs hs'
  · rw [eval_reinsertLast_node _ _ i hZ,
      canonicalInterpolant_eval _ (cupPrescription_collision ψ hψ s)]
  · simp only [map_add,map_mul,map_prod,map_sub,eval_C,eval_X,eval_rename]
    rw [eval_reinsertLast_node _ _ i hZ,
      canonicalInterpolant_eval _ (dividedCupPrescription_collision ψ hψ s),hzero,zero_mul,add_zero]
    rw [cupPrescription_factor,map_mul,eval_X]
    simp [hZ,T_ne_zero,Function.comp_apply]
  · simp only [map_mul,add_zero,eval_C,eval_X]
    rw [eval_reinsertLast_node _ _ i hZ,
      canonicalInterpolant_eval _ (dividedCupPrescription_collision ψ hψ s),cupPrescription_factor,map_mul,eval_X]
    simp [hZ,T_ne_zero,Function.comp_apply]

end PolynomialVacuumAlgebra

end OAI

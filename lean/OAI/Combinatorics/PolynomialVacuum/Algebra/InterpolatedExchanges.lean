import OAI.Combinatorics.PolynomialVacuum.Algebra.FirstExchanges
import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalCandidateEndpoints

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem eval_interpolateState {n : ℕ} (ψ : State n) (χ : State (n+1))
    (s : Fin (n+2) → Spin) (Z : Fin (n+2) → ℂ) :
    eval Z (interpolateState ψ χ s)=
      (lastPolynomial ψ χ s).eval₂ (eval (Z ∘ Fin.castSucc)) (T⁻¹*Z (Fin.last (n+1))) := by
  rw [interpolateState_eq_reinsert,eval_reinsertLast]

theorem eval₂_lastPolynomial_swap {n : ℕ} (p : Polynomial (MvPolynomial (Fin (n+1)) ℂ))
    (j : Fin n) (Xv : ℕ → ℂ) :
    (p.map (rename (Equiv.swap j.castSucc j.succ)).toRingHom).eval₂
      (eval (fun k : Fin (n+1) => Xv k.val)) (T⁻¹*Xv (n+1))=
    p.eval₂ (eval (fun k : Fin (n+1) => swapSite j.val Xv k.val))
      (T⁻¹*swapSite j.val Xv (n+1)) := by
  have hl : swapSite j.val Xv (n+1)=Xv (n+1) :=
    swapSite_other (by have:=j.isLt; omega) (by have:=j.isLt; omega) Xv
  rw [hl]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.map_add,Polynomial.eval₂_add] using congrArg₂ (·+·) hp hq
  | monomial k a =>
    simp only [Polynomial.map_monomial,Polynomial.eval₂_monomial]
    change eval (fun k => Xv k.val) (rename (Equiv.swap j.castSucc j.succ) a) * _=_
    rw [eval_rename]
    congr 2
    apply congrArg eval
    funext i
    simp only [Function.comp_apply,swapSite,Equiv.swap_apply_def,Fin.ext_iff,
      Fin.val_castSucc,Fin.val_succ]
    split_ifs <;> rfl

theorem interpolateState_first_exchanges {n : ℕ} (ψ : State n) (χ : State (n+1))
    (hψ : LowerExchange (liftState ψ) n) (hχ : LowerExchange (liftState χ) (n+1)) :
    LowerExchange (liftState (interpolateState ψ χ)) (n+1) := by
  intro j hj Xv
  let jf : Fin n := ⟨j,by omega⟩
  funext s
  have he := congrArg (fun p : Polynomial (MvPolynomial (Fin (n+1)) ℂ) =>
      p.eval₂ (eval (fun k => Xv k.val)) (T⁻¹*Xv (n+1)))
    (lastPolynomial_first_exchange ψ χ hψ hχ jf (fun k => s k.val))
  simp only [Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_sub,
    eval_polyExchangeNumerator,map_mul,map_sub,eval_C,eval_X,eval₂_lastPolynomial_swap] at he
  change (siteR j (Xv j) (Xv (j+1)) (liftState (interpolateState ψ χ) Xv)) s=_
  simp only [siteR,pairLinear,LinearMap.coe_mk,AddHom.coe_mk,pairAction,Pi.smul_apply,smul_eq_mul,
    liftState,liftPolyTensor,eval_interpolateState]
  convert he using 1
  · apply Finset.sum_congr rfl
    intro ab hab
    congr 2
    congr 1
    exact replacePair_restrict (pairLeft jf.castSucc) (pairRight jf.castSucc) s ab
  · rfl

end PolynomialVacuumAlgebra

end OAI

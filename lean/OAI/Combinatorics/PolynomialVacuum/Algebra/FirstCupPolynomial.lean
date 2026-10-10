import OAI.Combinatorics.PolynomialVacuum.Algebra.LastDegrees
import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalCandidateEndpoints
import OAI.Combinatorics.PolynomialVacuum.Algebra.CupSurfaceInterpolation

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def firstCupState {n : ℕ} (ψ : State n) : State (n+2) := fun s =>
  C ((1+T)*cup (s 0,s 1))*X 0 *
    (∏ j : Fin n, (X j.succ.succ-C (t^5)*X 0)*(X j.succ.succ-C (t^6)*X 0)) *
    rename (fun j : Fin n => j.succ.succ) (ψ (fun j => s j.succ.succ))

theorem lift_firstCupState {n : ℕ} (ψ : State n) (Xv : ℕ → ℂ) :
    liftState (firstCupState ψ) Xv=
      naturalFusion n 0 Xv • cupLinear 0 (liftState ψ (skipTwo 0 Xv)) := by
  funext s
  simp only [liftState,liftPolyTensor,firstCupState,map_mul,map_prod,map_sub,eval_C,
    eval_X,eval_rename,Fin.val_succ,naturalFusion,fusionProduct,
    fusionPair,skipTwo_zero_apply,Pi.smul_apply,smul_eq_mul,cupLinear,LinearMap.coe_mk,
    AddHom.coe_mk]
  simp only [Function.comp_def,Fin.val_succ,Fin.val_zero,Fin.val_one,Nat.add_assoc,Nat.reduceAdd,Nat.zero_add]
  rw [Fin.prod_univ_eq_prod_range (fun k => (Xv (k+2)-t^5*Xv 0)*(Xv (k+2)-t^6*Xv 0)) n]
  ring

theorem firstCupState_last_degree {n : ℕ} (ψ : State (n+1)) (s : Fin (n+3) → Spin)
    (d : ℕ) (hd : (ψ (fun j => s j.succ.succ)).degreeOf (Fin.last n) ≤ d) :
    (firstCupState ψ s).degreeOf (Fin.last (n+2)) ≤ d+2 := by
  have hh : ((Fin.last n).succ.succ : Fin (n+3))=Fin.last (n+2) := rfl
  have hr : (rename (fun j : Fin (n+1) => j.succ.succ)
      (ψ (fun j => s j.succ.succ))).degreeOf (Fin.last (n+2)) ≤ d := by
    rw [← hh,degreeOf_rename_of_injective (fun _ _ h => (Fin.succ_injective _) ((Fin.succ_injective _) h))]
    exact hd
  have h0 : (X (0 : Fin (n+3)) : MvPolynomial (Fin (n+3)) ℂ).degreeOf (Fin.last (n+2)) ≤ 0 := by
    exact le_of_eq (degreeOf_X_of_ne (by intro h; have:=congrArg Fin.val h; simp at this))
  have hc (k : ℕ) : (C (t^k)*X (0 : Fin (n+3)) : MvPolynomial (Fin (n+3)) ℂ).degreeOf (Fin.last (n+2)) ≤ 0 :=
    dconst_mul _ h0
  have hf (j : Fin (n+1)) :
      ((X j.succ.succ-C (t^5)*X 0)*(X j.succ.succ-C (t^6)*X 0) : MvPolynomial (Fin (n+3)) ℂ).degreeOf (Fin.last (n+2)) ≤ if j=Fin.last n then 2 else 0 := by
    by_cases hj : j=Fin.last n
    · subst j
      simp only [ite_true]
      apply (dmul (a:=1) (b:=1) ?_ ?_).trans (by omega)
      all_goals rw [sub_eq_add_neg]; apply dadd (by simp); rw [degreeOf_neg]; exact (hc _).trans (by omega)
    · simp only [ite_eq_right hj]
      have hx : (X j.succ.succ : MvPolynomial (Fin (n+3)) ℂ).degreeOf (Fin.last (n+2)) ≤ 0 := by
        exact le_of_eq (degreeOf_X_of_ne (by
          intro he
          have hv : n+2=j.val+1+1 := congrArg Fin.val he
          exact hj (Fin.ext (show j.val=n from by omega))))
      apply dmul (a:=0) (b:=0)
      all_goals rw [sub_eq_add_neg]; exact dadd hx (by rw [degreeOf_neg]; exact hc _)
  have hp : (∏ j : Fin (n+1), (X j.succ.succ-C (t^5)*X 0)*(X j.succ.succ-C (t^6)*X 0) : MvPolynomial (Fin (n+3)) ℂ).degreeOf (Fin.last (n+2)) ≤ 2 := by
    apply (degreeOf_prod_le _ _ _).trans
    exact (Finset.sum_le_sum (fun j _ => hf j)).trans (by simp)
  exact (dmul (dmul (dconst_mul _ h0) hp) hr).trans (by omega)

end PolynomialVacuumAlgebra

end OAI

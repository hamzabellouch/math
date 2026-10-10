import OAI.Combinatorics.PolynomialVacuum.Algebra.PrescriptionEvaluation
import OAI.Combinatorics.PolynomialVacuum.Algebra.PolynomialGenericity
import OAI.Combinatorics.PolynomialVacuum.Algebra.Candidate

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical PolynomialVacuumInterpolation

def extendFinite {α : Type*} {m : ℕ} (a₀ : α) (Z : Fin m → α) (k : ℕ) : α :=
  if h : k < m then Z ⟨k,h⟩ else a₀

@[simp] theorem extendFinite_fin {α : Type*} {m : ℕ} (a₀ : α) (Z : Fin m → α) (k : Fin m) :
    extendFinite a₀ Z k.val=Z k := by simp [extendFinite,k.isLt]

theorem eval_mergeVariable {ι : Type*} (i j : ι) (p : MvPolynomial ι ℂ) (Z : ι → ℂ) :
    eval Z (mergeVariable i j p)=eval (fun k => if k=i then Z j else Z k) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp only [map_add,hp,hr]
  | mul_X p k hp =>
    simp only [map_mul,mergeVariable_X,eval_X,hp]
    split_ifs <;> simp

 

theorem cupPrescription_collision {n : ℕ} (ψ : State n)
    (hψ : LowerExchange (liftState ψ) n) (s : Fin (n+2) → Spin) :
    CollisionCompatible (fun i => cupPrescription ψ i s) := by
  intro i j
  let κ : Fin (n+1) → Fin (n+1) := fun k => if k=i then j else k
  apply polynomial_eq_on_generic (genericGuard_ne_zero κ)
  intro Z hZ
  rw [eval_genericGuard] at hZ
  let Y : Fin (n+1) → ℂ := Z ∘ κ
  let X : ℕ → ℂ := extendFinite 0 Y
  have hG : GenericParameters n X := by
    intro a b ha hb
    have hga : a < n+1 := by omega
    have hgb : b < n+1 := by omega
    have hn := (Finset.prod_ne_zero_iff.mp hZ) (⟨a,hga⟩ : Fin (n+1)) (Finset.mem_univ _)
    have hn' := (Finset.prod_ne_zero_iff.mp hn) (⟨b,hgb⟩ : Fin (n+1)) (Finset.mem_univ _)
    simpa only [X,extendFinite,dite_eq_left hga,dite_eq_left hgb,Y,Function.comp_apply] using hn'
  have he : X i.val=X j.val := by
    simp [X,Y,κ]
  have h := naturalPrescription_collision_generic hψ (by omega : i.val ≤ n)
    (by omega : j.val ≤ n) X hG he
  rw [← cupPrescription_evaluation,← cupPrescription_evaluation] at h
  have hs := congrFun h (extendFinite Spin.zero s)
  simp only [liftPolyTensor,X,extendFinite_fin] at hs
  rw [eval_mergeVariable,eval_mergeVariable]
  convert hs using 2 <;> congr 1 <;> funext k <;>
    simp only [Y,Function.comp_apply,κ] <;> split_ifs <;> rfl

theorem dividedCupPrescription_collision {n : ℕ} (ψ : State n)
    (hψ : LowerExchange (liftState ψ) n) (s : Fin (n+2) → Spin) :
    CollisionCompatible (fun i => dividedCupPrescription ψ i s) := by
  intro i j
  have h := cupPrescription_collision ψ hψ s i j
  dsimp only at h ⊢
  rw [cupPrescription_factor,cupPrescription_factor,map_mul,map_mul] at h
  by_cases hij : j=i
  · subst j; rfl
  simp only [mergeVariable_X,ite_eq_right hij] at h
  exact mul_left_cancel₀ (MvPolynomial.X_ne_zero j) h

end PolynomialVacuumAlgebra

end OAI

import OAI.Combinatorics.PolynomialVacuum.Algebra.FirstCupInterpolation
import OAI.Combinatorics.PolynomialVacuum.Algebra.CupPointwiseSlide
import OAI.Combinatorics.PolynomialVacuum.Algebra.InterpolatedExchanges

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def cupPolynomial {n : ℕ} (ψ : State n) (i : ℕ) (s : ℕ → Spin) :
    MvPolynomial ℕ ℂ :=
  C ((1+T)*cup (s i,s (i+1)))*X i *
    (∏ k ∈ Finset.range n,
      (X (if k < i then k else k+2)-C (t^5)*X i)*(X (if k < i then k else k+2)-C (t^6)*X i)) *
    rename (fun j : Fin n => if j.val < i then j.val else j.val+2)
      (ψ (fun j => skipTwo i s j.val))

@[simp] theorem eval_cupPolynomial {n : ℕ} (ψ : State n) (i : ℕ) (s : ℕ → Spin) (Y : ℕ → ℂ) :
    eval Y (cupPolynomial ψ i s)=(naturalFusion n i Y • cupLinear i (liftState ψ (skipTwo i Y))) s := by
  simp only [cupPolynomial,map_mul,map_prod,map_sub,eval_C,eval_X,eval_rename,
    liftState,liftPolyTensor,naturalFusion,fusionProduct,fusionPair,Pi.smul_apply,smul_eq_mul,
    cupLinear,LinearMap.coe_mk,AddHom.coe_mk,Function.comp_def,skipTwo]
  have h1 : (fun j : Fin n => Y (if j.val < i then j.val else j.val+2))=
      (fun j : Fin n => if j.val < i then Y j.val else Y (j.val+2)) := by funext j; split_ifs <;> rfl
  have h2 (k : ℕ) : Y (if k < i then k else k+2)=if k < i then Y k else Y (k+2) := by split_ifs <;> rfl
  simp only [h2]
  ring

noncomputable def cupSlideGuard (i : ℕ) : MvPolynomial ℕ ℂ :=
  ((C (t^2)*X (i+1)-X i)*(C T*X (i+1)-X i))*
    ((C (t^2)*(C T*X (i+1))-X i)*(C T*(C T*X (i+1))-X i))

@[simp] theorem eval_cupSlideGuard (i : ℕ) (Y : ℕ → ℂ) :
    eval Y (cupSlideGuard i)=exchangeDenominator (Y (i+1)) (Y i)*
      exchangeDenominator (T*Y (i+1)) (Y i) := by
  simp [cupSlideGuard,exchangeDenominator]

theorem cupSlideGuard_surface_ne_zero (i : ℕ) :
    cupSpecialize (i+1) (i+2) (cupSlideGuard i)≠0 := by
  intro he
  have hv := congrArg (eval (fun j : ℕ => if j=i then (1:ℂ) else 0)) he
  simp only [map_zero,eval_cupSpecialize,eval_cupSlideGuard] at hv
  have h0 : i≠i+2 := by omega
  have h1 : i+1≠i+2 := by omega
  norm_num [Function.update_of_ne h0,Function.update_of_ne h1,
    show i+1≠i by omega,exchangeDenominator] at hv

theorem cupSurface_eq_of_generic (a b : ℕ) (hab : a≠b) (p r G : MvPolynomial ℕ ℂ)
    (hG : cupSpecialize a b G≠0)
    (h : ∀ Y, Y b=T*Y a → eval Y G≠0 → eval Y p=eval Y r) :
    cupSpecialize a b p=cupSpecialize a b r := by
  apply polynomial_eq_on_generic hG
  intro X hX
  simp only [eval_cupSpecialize] at hX ⊢
  apply h _ _ hX
  simp [hab]

theorem cupAt_step {n : ℕ} (Ψ : State (n+2)) (ψ : State n) (i : ℕ)
    (hΨ : LowerExchange (liftState Ψ) (n+1)) (hi : i+2 < n+1)
    (hc : CupAt (liftState Ψ) (liftState ψ) n i) :
    CupAt (liftState Ψ) (liftState ψ) n (i+1) := by
  intro Y hY
  funext s
  have he : cupSpecialize (i+1) (i+2) (coordinatePolynomial Ψ s)=
      cupSpecialize (i+1) (i+2) (cupPolynomial ψ (i+1) s) := by
    apply cupSurface_eq_of_generic _ _ (by omega) _ _ (cupSlideGuard i) (cupSlideGuard_surface_ne_zero i)
    intro X hX hG
    simp only [eval_coordinatePolynomial,eval_cupPolynomial]
    exact congrFun (cupAt_step_generic hΨ hi hc X hX (by simpa using hG)) s
  simpa using eval_eq_of_cupSurface_eq (i+1) (i+2) _ _ he Y hY

 

theorem cupAt_of_first {n : ℕ} (Ψ : State (n+2)) (ψ : State n)
    (hΨ : LowerExchange (liftState Ψ) (n+1))
    (hc : FirstCupReduction (liftState Ψ) (liftState ψ) n) :
    ∀ i, i < n → CupAt (liftState Ψ) (liftState ψ) n i := by
  intro i hi
  induction i with
  | zero => exact hc
  | succ i ih => exact cupAt_step Ψ ψ i hΨ (by omega) (ih (by omega))

end PolynomialVacuumAlgebra

end OAI

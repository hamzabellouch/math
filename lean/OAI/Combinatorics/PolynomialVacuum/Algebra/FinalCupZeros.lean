import OAI.Combinatorics.PolynomialVacuum.Algebra.PenultimateCup
import OAI.Combinatorics.PolynomialVacuum.Algebra.ExchangeDifference
import OAI.Combinatorics.PolynomialVacuum.Algebra.FirstCupInterpolation

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

@[simp] theorem eval_partialTrainGuard (n i : ℕ) (Y : ℕ → ℂ) :
    eval Y (partialTrainGuard n i)=trainDenominator (T*Y i) Y (i+1) (n-i-1) := by
  simp [partialTrainGuard,trainDenominator_prod]

theorem partialTrainGuard_surface {n i : ℕ} (hi : i < n) :
    cupSpecialize i n (partialTrainGuard n i)≠0 := by
  intro he
  have hv := congrArg (eval (fun j : ℕ => if j=i then (0:ℂ) else 1)) he
  simp only [map_zero,eval_cupSpecialize,eval_partialTrainGuard,trainDenominator_prod] at hv
  have hprod : (∏ j ∈ Finset.range (n-i-1), exchangeDenominator
      (T*Function.update (fun k : ℕ => if k=i then (0:ℂ) else 1) n
        (T*(if i=i then (0:ℂ) else 1)) i)
      (Function.update (fun k : ℕ => if k=i then (0:ℂ) else 1) n
        (T*(if i=i then (0:ℂ) else 1)) (i+1+j)))=1 := by
    apply Finset.prod_eq_one
    intro j hj
    have hj' := Finset.mem_range.mp hj
    simp [Function.update_of_ne (by omega : i≠n),Function.update_of_ne (by omega : i+1+j≠n),
      show i+1+j≠i by omega,exchangeDenominator]
  simp only [ite_true,update_nat_decidable] at hprod hv
  rw [hprod] at hv
  exact one_ne_zero hv

theorem finalDifference_penultimate_generic {n i : ℕ} {Ψ ψ : NatSpectralTensor}
    (hex : LowerExchange Ψ (n+1)) (hnode : NaturalCupNodes Ψ ψ n)
    (hi : i < n) (hc : CupAt Ψ ψ n i) (X : ℕ → ℂ) (hX : X n=T*X i)
    (hD : trainDenominator (T*X i) X (i+1) (n-i-1)≠0)
    (hcross : siteR n (T*X i) (X (n+1)) (penultimatePrescription ψ n i X)=
      exchangeDenominator (T*X i) (X (n+1)) • naturalPrescription ψ n i (swapSite n X)) :
    exchangeDifference Ψ n X=0 := by
  have hs : swapSite n X i=X i := swapSite_other (by omega) (by omega) X
  unfold exchangeDifference
  rw [penultimateCup_generic hex hi hc X hX hD,hX,hcross]
  rw [hnode (swapSite n X) i (by omega) (by simpa only [swapSite_right,hs] using hX)]
  exact sub_self _

theorem finalDifference_penultimate {n i : ℕ} (Ψ : State (n+2)) (ψ : State n)
    (hex : LowerExchange (liftState Ψ) (n+1))
    (hnode : NaturalCupNodes (liftState Ψ) (liftState ψ) n)
    (hi : i < n) (hc : CupAt (liftState Ψ) (liftState ψ) n i)
    (X : ℕ → ℂ) (hX : X n=T*X i) : exchangeDifference (liftState Ψ) n X=0 := by
  funext s
  have he : cupSpecialize i n (exchangeDiscrepancy Ψ n s)=cupSpecialize i n 0 := by
    apply cupSurface_eq_of_generic i n (by omega) _ _ (partialTrainGuard n i) (partialTrainGuard_surface hi)
    intro Y hY hG
    simp only [eval_exchangeDiscrepancy,map_zero]
    exact congrFun (finalDifference_penultimate_generic hex hnode hi hc Y hY
      (by simpa using hG) (penultimatePrescription_last_crossing ψ hi Y)) s
  have he' := eval_eq_of_cupSurface_eq i n _ _ he X hX
  simpa only [eval_exchangeDiscrepancy,map_zero,exchangeDifference,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using he'

theorem reverseExchangeGuard_surface {n i : ℕ} (hi : i < n) :
    cupSpecialize i (n+1) (polyExchangeDenominator (X (n+1)) (X n))≠0 := by
  intro he
  have hv := congrArg (eval (fun j : ℕ => if j=i then (0:ℂ) else 1)) he
  simp [eval_cupSpecialize,show n≠i by omega,exchangeDenominator] at hv

theorem finalDifference_last {n i : ℕ} (Ψ : State (n+2)) (ψ : State n)
    (hex : LowerExchange (liftState Ψ) (n+1))
    (hnode : NaturalCupNodes (liftState Ψ) (liftState ψ) n)
    (hi : i < n) (hc : CupAt (liftState Ψ) (liftState ψ) n i)
    (X : ℕ → ℂ) (hX : X (n+1)=T*X i) : exchangeDifference (liftState Ψ) n X=0 := by
  funext s
  have he : cupSpecialize i (n+1) (exchangeDiscrepancy Ψ n s)=cupSpecialize i (n+1) 0 := by
    apply cupSurface_eq_of_generic i (n+1) (by omega) _ _
      (polyExchangeDenominator (MvPolynomial.X (n+1)) (MvPolynomial.X n)) (reverseExchangeGuard_surface hi)
    intro Y hY hG
    simp only [eval_polyExchangeDenominator,eval_X] at hG
    have hh := finalDifference_penultimate Ψ ψ hex hnode hi hc (swapSite n Y)
      (by simpa only [swapSite_left,swapSite_other (by omega : i≠n) (by omega : i≠n+1)] using hY)
    simp only [exchangeDifference,swapSite_left,swapSite_right,swapSite_twice,sub_eq_zero] at hh
    have hh' := congrArg (siteR n (Y n) (Y (n+1))) hh
    rw [siteR_unitary,map_smul] at hh'
    have hs : exchangeDenominator (Y (n+1)) (Y n) •
        (siteR n (Y n) (Y (n+1)) (liftState Ψ Y))=
      exchangeDenominator (Y (n+1)) (Y n) •
        (exchangeDenominator (Y n) (Y (n+1)) • liftState Ψ (swapSite n Y)) := by
      simpa only [smul_smul,mul_comm] using hh'.symm
    have hf := (smul_right_injective _ hG) hs
    simp only [eval_exchangeDiscrepancy,map_zero]
    exact sub_eq_zero.mpr (congrFun hf s)
  have he' := eval_eq_of_cupSurface_eq i (n+1) _ _ he X hX
  simpa only [eval_exchangeDiscrepancy,map_zero,exchangeDifference,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using he'

end PolynomialVacuumAlgebra

end OAI

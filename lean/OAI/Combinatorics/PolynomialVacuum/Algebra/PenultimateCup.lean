import OAI.Combinatorics.PolynomialVacuum.Algebra.PartialCupScalar
import OAI.Combinatorics.PolynomialVacuum.Algebra.InterpolatedCups

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

noncomputable def penultimatePrescription (ψ : NatSpectralTensor) (n i : ℕ)
    (X : ℕ → ℂ) : SpinTensor ℕ ℂ :=
  ((1+T)*X i*leftFusion i X*fusionPair (X i) (X (n+1))) •
    (braidTrain (T*X i) X (i+1) (n-i-1)*cupLinear i)
      (ψ (skipOne i (skipOne n X)))

theorem penultimateCup_generic {Ψ ψ : NatSpectralTensor} {n i : ℕ}
    (hΨ : LowerExchange Ψ (n+1)) (hi : i < n) (hc : CupAt Ψ ψ n i)
    (X : ℕ → ℂ) (hX : X n=T*X i)
    (hD : trainDenominator (T*X i) X (i+1) (n-i-1)≠0) :
    Ψ X=penultimatePrescription ψ n i X := by
  have he := braidTrain_pull_exchange hΨ (i+1) (n-i-1) (by omega) (T*X i) X
  rw [show i+1+(n-i-1)=n by omega,← hX,Function.update_eq_self] at he
  rw [hX] at he
  have hcup : pullSite (i+1) (n-i-1) (T*X i) X (i+1)=
      T*pullSite (i+1) (n-i-1) (T*X i) X i := by
    simp [pullSite_before (by omega : i < i+1)]
  rw [hc _ hcup,naturalFusion_pull_penultimate n i hi X,map_smul,
    skipTwo_pullSite,show i+1+(n-i-1)=n by omega] at he
  apply (smul_right_injective _ hD)
  simpa only [penultimatePrescription,Module.End.mul_apply,smul_smul,mul_comm] using he.symm

theorem penultimatePrescription_last_crossing {n i : ℕ} (ψ : State n)
    (hi : i < n) (X : ℕ → ℂ) :
    siteR n (T*X i) (X (n+1)) (penultimatePrescription (liftState ψ) n i X)=
      exchangeDenominator (T*X i) (X (n+1)) •
        naturalPrescription (liftState ψ) n i (swapSite n X) := by
  have hxi : swapSite n X i=X i := swapSite_other (by omega) (by omega) X
  have hp : liftState ψ (skipOne i (swapSite n X))=
      liftState ψ (skipOne i (skipOne n X)) := by
    apply liftState_params_congr
    intro j hj
    by_cases h : j < i
    · simp [skipOne,h,swapSite_other (by omega : j≠n) (by omega : j≠n+1),hj]
    · by_cases h' : j+1=n
      · simp [skipOne,h,h',swapSite_left]
      · simp [skipOne,h,swapSite_other h' (by omega : j+1≠n+1),show j+1 < n by omega]
  have ht : braidTrain (T*X i) (swapSite n X) (i+1) (n-i)=
      siteR n (T*X i) (X (n+1))*braidTrain (T*X i) X (i+1) (n-i-1) := by
    rw [show n-i=(n-i-1)+1 by omega,braidTrain_snoc,
      show i+1+(n-i-1)=n by omega,swapSite_left]
    congr 1
    apply braidTrain_congr
    intro j hj hj'
    exact swapSite_other (by omega) (by omega) X
  simp only [penultimatePrescription,naturalPrescription,hxi,leftFusion_swap_after hi,hp,ht,
    map_smul,Module.End.mul_apply,smul_smul,fusionPair_denominator]
  congr 1
  ring

end PolynomialVacuumAlgebra

end OAI

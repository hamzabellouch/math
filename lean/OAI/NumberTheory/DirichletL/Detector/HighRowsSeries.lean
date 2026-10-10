import OAI.NumberTheory.DirichletL.Detector.HighRowsWeights
import OAI.NumberTheory.DirichletL.Detector.HighRowsRecurrence
import OAI.NumberTheory.DirichletL.Detector.LocalSeries

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)

def rowMarkedTerm (eta a X W V rho : ℂ) (j e l k m : ℕ) : ℂ :=
  if e+3*l=0 then 0 else
    rowWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1)) X W V rho
      (positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) (e+3*l-1) k (j+6*m)) e l k m

include hc in
theorem rowMarkedTerm_step (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (j e l k m : ℕ) (ht : 0<e+3*l) :
    rowMarkedTerm p hp hg eta a X W V rho j e (l+2) k (m+1)=
      evenRatio (Ideal.absNorm (Ideal.span {p})) a X V *
        rowMarkedTerm p hp hg eta a X W V rho j e l k m := by
  unfold rowMarkedTerm
  rw [ite_eq_right (by omega),ite_eq_right (by omega),
    show e+3*(l+2)-1=(e+3*l-1)+6 by omega,
    show j+6*(m+1)=(j+6*m)+6 by omega,
    positiveScalar_step_six p hp hg hc]
  exact rowWeightedScalar_step_two _ _ _ _ _ _ _ _ _ _ _ (primeNorm_ne_zero p hp)
    (localGamma_conjugate_three_sq p hp hg hc) (actualSextic_neg_one_sq _ hg) hρ e l k m

theorem rowMarkedTerm_higher_outer (eta a X W V rho : ℂ) (j e l k m : ℕ) :
    rowMarkedTerm p hp hg eta a X W V rho j e l (k+2) m=0 := by
  unfold rowMarkedTerm
  split_ifs
  · rfl
  · rw [positiveScalar_kge_two p hp,rowWeightedScalar_zero]

end SevenEighths.ProbeEuler
end

end OAI

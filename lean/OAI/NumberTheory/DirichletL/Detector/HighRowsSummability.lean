import OAI.NumberTheory.DirichletL.Detector.HighRowsSeries
import OAI.NumberTheory.DirichletL.Detector.HighRowsDiagonal

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma geometric_indicator_summable (V A : ℂ) (hV : ‖V‖<1) (p : ℕ→Prop) :
    Summable (fun m=>(if p m then A else 0)*V^m) := by
  convert (((hasSum_geometric_of_norm_lt_one hV).summable.mul_left A).indicator {m | p m}) using 1
  funext m
  by_cases hm : p m <;> simp [hm]

lemma gaussValuationTable_geometric_summable (Q G V : ℂ) (hV : ‖V‖<1)
    (r n : ℕ) (j : ℕ→ℕ) :
    Summable (fun m=>gaussValuationTable Q G r n (j m)*V^m) := by
  by_cases hr : 6∣r
  · have ha := geometric_indicator_summable V (Q^(n+1)) hV (fun m=>n+1≤j m)
    have hb := geometric_indicator_summable V (Q^n) hV (fun m=>n≤j m)
    convert ha.sub hb using 1
    funext m
    simp only [gaussValuationTable,ite_eq_left hr,sub_mul]
    split_ifs <;> rfl
  · convert geometric_indicator_summable V (Q^n*G) hV (fun m=>j m=n) using 1
    funext m
    simp only [gaussValuationTable,ite_eq_right hr]
    split_ifs <;> rfl

theorem positiveScalar_geometric_summable (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (n k : ℕ) (j : ℕ→ℕ) (V : ℂ) (hV : ‖V‖<1) :
    Summable (fun m=>positiveScalar p hp.ne_zero (actualSextic (Ideal.span {p}) hg) n k (j m)*V^m) := by
  simp only [positiveScalar_actual_table p hp hg hc]
  by_cases hk : k=0
  · simp only [ite_eq_left hk]
    exact gaussValuationTable_geometric_summable _ _ V hV (n+1) n j
  · simp only [ite_eq_right hk]
    have hs := (gaussValuationTable_geometric_summable (Ideal.absNorm (Ideal.span {p}))
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg^n) 1) V hV n n (fun m=>j m-1)).mul_left
      (((actualSextic (Ideal.span {p}) hg (-1))⁻¹)*primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
    convert hs.indicator {m | k=1 ∧ 1≤j m} using 1
    funext m
    by_cases hm : k=1 ∧ 1≤j m <;> simp [hm,mul_assoc]

end SevenEighths.ProbePrimePower
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
include hc

theorem rowMarkedTerm_frequency_summable (eta a X W V rho : ℂ) (hV : ‖V‖<1)
    (j e l k : ℕ) : Summable (fun m=>rowMarkedTerm p hp hg eta a X W V rho j e l k m) := by
  by_cases ht : e+3*l=0
  · simp only [rowMarkedTerm,ite_eq_left ht,summable_zero]
  · simp only [rowMarkedTerm,ite_eq_right ht,rowWeightedScalar,weightedScalar]
    have hs := SevenEighths.ProbePrimePower.positiveScalar_geometric_summable p hp hg hc (e+3*l-1) k (fun m=>j+6*m) V hV
    convert hs.mul_left ((rho^k/rho^(e+3*l)) *
      ((-eta*X/primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)^e *
        (a*X^3/(Ideal.absNorm (Ideal.span {p}):ℂ))^l *
        localCubePhase (star (localGamma p hp.ne_zero hg 3))
          (actualSextic (Ideal.span {p}) hg (-1)) e l k) *W^k) using 1
    funext m
    ring

theorem rowMarkedTerm_zero_lower_edge (eta a X W V rho : ℂ)
    (j e l k : ℕ) (hj : j<6) (ht : 0<e+3*l) :
    rowMarkedTerm p hp hg eta a X W V rho j e (l+2) k 0=0 := by
  unfold rowMarkedTerm
  rw [ite_eq_right (by omega),positiveScalar_zero_below p hp hg hc _ _ _ (by omega),
    rowWeightedScalar_zero]

theorem rowMarkedFamily_hasSum (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j e l k : ℕ) (hj : j<6) (ht : 0<e+3*l) :
    HasSum (fun r=>∑' m,rowMarkedTerm p hp hg eta a X W V rho j e (l+2*r) k m)
      ((∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m)/
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  apply diagonal_recurrence_hasSum
  · intro r m
    rw [show l+2*(r+1)=(l+2*r)+2 by omega]
    exact rowMarkedTerm_step p hp hg hc eta a X W V rho hρ j e (l+2*r) k m (by omega)
  · intro r
    rw [show l+2*(r+1)=(l+2*r)+2 by omega]
    exact rowMarkedTerm_zero_lower_edge p hp hg hc eta a X W V rho j e (l+2*r) k hj (by omega)
  · simpa only [mul_zero,add_zero] using rowMarkedTerm_frequency_summable p hp hg hc eta a X W V rho hV j e l k
  · exact hR

end SevenEighths.ProbeEuler
end

end OAI

import OAI.NumberTheory.DirichletL.Detector.HighRowsSummability

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def rowInner (eta a X W V rho : ℂ) (j e l : ℕ) : ℂ :=
  ∑' k, ∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l k m

def rowMarkedSeries (eta a X W V rho : ℂ) (j : ℕ) : ℂ :=
  ∑ e : Fin 2, ∑' l,rowInner p hp hg eta a X W V rho j e.val l

lemma rowInner_two (eta a X W V rho : ℂ) (j e l : ℕ) :
    rowInner p hp hg eta a X W V rho j e l=
      (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l 0 m)+
      (∑' m,rowMarkedTerm p hp hg eta a X W V rho j e l 1 m) := by
  apply tsum_two_of_rest_zero
  intro k
  simp only [rowMarkedTerm_higher_outer,tsum_zero]

@[simp] lemma rowInner_zero (eta a X W V rho : ℂ) (j : ℕ) :
    rowInner p hp hg eta a X W V rho j 0 0=0 := by
  simp only [rowInner,rowMarkedTerm,mul_zero,add_zero,ite_true,tsum_zero]

include hc in
theorem rowInner_family_hasSum (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j e l : ℕ) (hj : j<6) (ht : 0<e+3*l) :
    HasSum (fun r=>rowInner p hp hg eta a X W V rho j e (l+2*r))
      (rowInner p hp hg eta a X W V rho j e l/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
  have h0 := rowMarkedFamily_hasSum p hp hg hc eta a X W V rho hρ hV hR j e l 0 hj ht
  have h1 := rowMarkedFamily_hasSum p hp hg hc eta a X W V rho hρ hV hR j e l 1 hj ht
  convert h0.add h1 using 1
  · funext r
    exact rowInner_two p hp hg eta a X W V rho j e (l+2*r)
  · rw [rowInner_two,add_div]

include hc in

theorem rowMarkedSeries_four_families (eta a X W V rho : ℂ) (hρ : rho^6=1)
    (hV : ‖V‖<1) (hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a X V‖<1)
    (j : ℕ) (hj : j<6) :
    rowMarkedSeries p hp hg eta a X W V rho j=
      (rowInner p hp hg eta a X W V rho j 0 2+
       rowInner p hp hg eta a X W V rho j 1 0+
       rowInner p hp hg eta a X W V rho j 0 1+
       rowInner p hp hg eta a X W V rho j 1 1)/
        (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V) := by
  have h02 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 2 hj (by omega)
  have h10 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 1 0 hj (by omega)
  have h01 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 0 1 hj (by omega)
  have h11 := rowInner_family_hasSum p hp hg hc eta a X W V rho hρ hV hR j 1 1 hj (by omega)
  have he0 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r))
      (rowInner p hp hg eta a X W V rho j 0 2/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    have hshift : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*(r+1)))
        (rowInner p hp hg eta a X W V rho j 0 2/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
      convert h02 using 1
      funext r
      congr 1
      omega
    have h := hshift.sum_range_add (f:=fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r)) (k:=1)
    simpa only [Finset.sum_range_one,mul_zero,rowInner_zero,zero_add] using h
  have he1 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 1 (2*r))
      (rowInner p hp hg eta a X W V rho j 1 0/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [zero_add] using h10
  have ho0 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 0 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 0 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [Nat.add_comm 1] using h01
  have ho1 : HasSum (fun r=>rowInner p hp hg eta a X W V rho j 1 (2*r+1))
      (rowInner p hp hg eta a X W V rho j 1 1/(1-evenRatio (Ideal.absNorm (Ideal.span {p})) a X V)) := by
    simpa only [Nat.add_comm 1] using h11
  unfold rowMarkedSeries
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one]
  rw [(he0.even_add_odd ho0).tsum_eq,(he1.even_add_odd ho1).tsum_eq]
  ring

end SevenEighths.ProbeEuler
end

end OAI

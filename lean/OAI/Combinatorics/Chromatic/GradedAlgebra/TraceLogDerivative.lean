import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.PowerSeriesSplitLeading
import OAI.Combinatorics.Chromatic.GradedAlgebra.NoncommSeriesCalculus

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {R K : Type*} [Ring R] [Algebra ℚ R] [CommRing K] [Algebra ℚ K]
variable (τ : R→ₗ[ℚ] K) (hτ : ∀a b,τ (a*b)=τ (b*a))
include hτ in
lemma trace_log_derivative (F : PowerSeries R) (hF : constantCoeff F=1) :
    traceSeries τ (ncDerivative (FormalLog.log F))=
      traceSeries τ (ncDerivative F*invOfUnit F 1) := by
  ext n
  simp only [coeff_traceSeries,coeff_ncDerivative,FormalLog.log,coeff_mk,
    map_nsmul,map_sum,LinearMap.map_smul,Finset.smul_sum]
  rw [geometric_mul_coeff F (ncDerivative F) hF n]
  simp only [Finset.mul_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have H:=congrArg (coeff n) (trace_derivative_power' τ hτ (F-1) k)
  simp only [coeff_traceSeries,coeff_ncDerivative,map_nsmul,
    map_sub,ncDerivative_one,sub_zero] at H
  rw [smul_comm (n+1) ((-1:ℚ)^k/(k+1:ℕ)),H]
  rw [←Nat.cast_smul_eq_nsmul ℚ,smul_smul,div_mul_cancel₀ _ (by positivity : ((k+1:ℕ):ℚ)≠0)]
  have Hpow : (-(F-1))^k=(-1:ℚ)^k • (F-1)^k := by
    rw [←smul_pow]
    simp
  rw [Hpow,mul_smul_comm,coeff_smul,LinearMap.map_smul]
end
end ElementaryPositivity.FormalLog

end
section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {R K : Type*} [Ring R] [Algebra ℚ R] [CommRing K] [Algebra ℚ K]
variable (τ : R→ₗ[ℚ] K) (hτ : ∀a b,τ (a*b)=τ (b*a))
omit [Algebra ℚ R] in
lemma inverse_product (F G : PowerSeries R) (hF : constantCoeff F=1)
    (hG : constantCoeff G=1) : invOfUnit (F*G) 1=invOfUnit G 1*invOfUnit F 1 := by
  have H : (F*G)*(invOfUnit G 1*invOfUnit F 1)=1 := by
    rw [mul_assoc,←mul_assoc G,PowerSeries.mul_invOfUnit G 1 hG,one_mul,
      PowerSeries.mul_invOfUnit F 1 hF]
  have H' :=congrArg (fun x : PowerSeries R=>invOfUnit (F*G) 1*x) H
  rw [←mul_assoc,PowerSeries.invOfUnit_mul (F*G) 1 (by simp [hF,hG]),one_mul,mul_one] at H'
  exact H'.symm

include hτ in
lemma trace_log_product (F G : PowerSeries R) (hF : constantCoeff F=1)
    (hG : constantCoeff G=1) :
    traceSeries τ (FormalLog.log (F*G))=
      traceSeries τ (FormalLog.log F)+traceSeries τ (FormalLog.log G) := by
  have H : traceSeries τ (ncDerivative (FormalLog.log (F*G)))=
      traceSeries τ (ncDerivative (FormalLog.log F))+
      traceSeries τ (ncDerivative (FormalLog.log G)) := by
    rw [trace_log_derivative τ hτ (F*G) (by simp [hF,hG]),ncDerivative_mul,
      inverse_product F G hF hG,add_mul,map_add,
      trace_log_derivative τ hτ F hF,trace_log_derivative τ hτ G hG]
    congr 1
    · simp only [mul_assoc]
      rw [←mul_assoc G,PowerSeries.mul_invOfUnit G 1 hG,one_mul]
    · rw [mul_assoc F,traceSeries_cyclic τ hτ]
      simp only [mul_assoc]
      rw [PowerSeries.invOfUnit_mul F 1 hF,mul_one]
  ext n
  cases n with
  | zero=>simp only [map_add,coeff_traceSeries,coeff_zero_eq_constantCoeff,log_constant,
      map_zero,add_zero]
  | succ n=>
    have HH:=congrArg (coeff n) H
    simp only [map_add,coeff_traceSeries,coeff_ncDerivative,map_nsmul] at HH
    have HHH : ((n+1:ℕ):ℚ) • τ (coeff (n+1) (FormalLog.log (F*G)))=
        ((n+1:ℕ):ℚ) • (τ (coeff (n+1) (FormalLog.log F))+
          τ (coeff (n+1) (FormalLog.log G))) := by
      simpa only [Nat.cast_smul_eq_nsmul,nsmul_add] using HH
    have hnn : ((n+1:ℕ):ℚ)≠0 :=by positivity
    have H4:=congrArg (fun x:K=>(((n+1:ℕ):ℚ)⁻¹) • x) HHH
    simpa only [smul_smul,inv_mul_cancel₀ hnn,one_smul,map_add,coeff_traceSeries] using H4
end
end ElementaryPositivity.FormalLog

end

end OAI

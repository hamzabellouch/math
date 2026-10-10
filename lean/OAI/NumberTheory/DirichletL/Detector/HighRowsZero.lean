import OAI.NumberTheory.DirichletL.Detector.HighRowsPrime

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : goodLambda∉Ideal.span {p})

def rowZeroIndexTerm (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ) (j k m : ℕ) : ℂ :=
  (if k=0 then 1 else (χ^k) (Ideal.Quotient.mk _ (p^(j+6*m))))*W^k*V^m

theorem sourceRowTerm_zero (eta a rho x w z : ℂ) (j k m : ℕ) :
    sourceRowTerm p hp hg eta a rho x w z j 0 0 k m=
      rowZeroIndexTerm p (actualSextic (Ideal.span {p}) hg)
        (rho*((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)))
        (coordV (Ideal.absNorm (Ideal.span {p})) z) j k m := by
  unfold sourceRowTerm
  rw [sourceWeightedScalar_actual p hp hg]
  simp only [rowZeroIndexTerm,sourceScalar,weightedScalar,localCubePhase,
    coordV,Complex.ofReal_natCast,mul_zero,add_zero,pow_zero,one_mul,mul_one,
    zero_mul,Nat.choose_zero_succ,ite_true,div_one,mul_pow]
  ring

omit [(Ideal.span {p}).IsMaximal] in
lemma rowZeroIndex_zero (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j : ℕ) (hV : ‖V‖<1) :
    HasSum (fun m=>rowZeroIndexTerm p χ W V j 0 m) (1/(1-V)) := by
  simpa only [rowZeroIndexTerm,ite_true,pow_zero,one_mul,one_div] using
    hasSum_geometric_of_norm_lt_one hV

include hp in
theorem rowZeroIndex_pos_ramified (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j k m : ℕ) (hj : j≠0) (hk : k≠0) : rowZeroIndexTerm p χ W V j k m=0 := by
  rw [rowZeroIndexTerm,ite_eq_right hk,zero_index_scalar p hp χ k (j+6*m) hk,
    ite_eq_right (by omega),zero_mul,zero_mul]

include hp in
theorem rowZeroIndexSeries_eq (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (W V : ℂ)
    (j : ℕ) (hW : ‖W‖<1) (hV : ‖V‖<1) :
    (∑' k,∑' m,rowZeroIndexTerm p χ W V j k m)=
      1/(1-V)+(if j=0 then W/(1-W) else 0) := by
  by_cases hj : j=0
  · subst j
    simp only [rowZeroIndexTerm,zero_add,ite_true]
    exact zeroIndexSeries_eq p hp χ W V hW hV
  · rw [ite_eq_right hj,add_zero]
    rw [tsum_eq_single 0]
    · exact (rowZeroIndex_zero p χ W V j hV).tsum_eq
    · intro k hk
      simp only [rowZeroIndex_pos_ramified p hp χ W V j k _ hj hk,tsum_zero]

end SevenEighths.ProbeEuler
end

end OAI

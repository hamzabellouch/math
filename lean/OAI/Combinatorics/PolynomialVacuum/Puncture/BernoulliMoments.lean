import OAI.Combinatorics.PolynomialVacuum.Puncture.ReferenceEvaluation

namespace OAI

namespace PolynomialVacuumCylinder
open Real MeasureTheory

 
noncomputable def referenceBernoulliMoment (m : ℕ) : ℝ :=
  (8/3 : ℝ)^(2*m+2) *
    ((-1 : ℝ)^(m+2)*((2 : ℝ)^(2*m+2)-1)*(bernoulli (2*m+2) : ℝ)) /
      (2*(2*(m : ℝ)+2))

private theorem reference_moment_arithmetic (m : ℕ) (b : ℝ) :
    ((2*m+1).factorial : ℝ)/(3*Real.pi/8)^(2*m+2)*
      ((1-1/(2 : ℝ)^(2*m+2))*
       ((-1 : ℝ)^(m+2)*(2 : ℝ)^(2*m+1)*Real.pi^(2*m+2)*b/
        ((2*m+2).factorial : ℝ))) =
    (8/3 : ℝ)^(2*m+2)*((-1 : ℝ)^(m+2)*((2 : ℝ)^(2*m+2)-1)*b)/
      (2*(2*(m : ℝ)+2)) := by
  have hf : ((2*m+2).factorial : ℝ) =
      (2*(m : ℝ)+2)*((2*m+1).factorial : ℝ) := by
    rw [show 2*m+2=(2*m+1)+1 by omega,Nat.factorial_succ]
    push_cast
    ring
  have hfact : ((2*m+1).factorial : ℝ)≠0 := by positivity
  have hpi : Real.pi≠0 := Real.pi_ne_zero
  have htwo : (2 : ℝ)^(2*m+2) = 2*(2 : ℝ)^(2*m+1) := by
    rw [show 2*m+2=(2*m+1)+1 by omega,pow_succ]
    ring
  rw [hf]
  simp only [mul_pow,div_pow]
  field_simp
  rw [htwo]
  ring

 

theorem reference_moment_bernoulli (m : ℕ) :
    (∫ x : ℝ,x^(2*m)*denominatorReferenceWeight x)=referenceBernoulliMoment m := by
  rw [reference_moment_integral,odd_moment_zeta]
  have hz := (hasSum_zeta_nat (Nat.succ_ne_zero m)).tsum_eq
  rw [show 2*(m+1)=2*m+2 by omega] at hz
  rw [show m+1+1=m+2 by omega,show 2*m+2-1=2*m+1 by omega] at hz
  rw [hz]
  exact reference_moment_arithmetic m (bernoulli (2*m+2) : ℝ)

noncomputable def referenceBernoulliMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun j k=>referenceBernoulliMoment (j.val+k.val)

 

theorem denominatorReferenceMatrix_eq_bernoulli (n : ℕ) :
    denominatorReferenceMatrix n=referenceBernoulliMatrix n := by
  ext j k
  change (∫ p : ℝ,p^(2*j.val+2*k.val)*denominatorReferenceWeight p)=
    referenceBernoulliMoment (j.val+k.val)
  rw [show 2*j.val+2*k.val=2*(j.val+k.val) by omega]
  exact reference_moment_bernoulli _

end PolynomialVacuumCylinder

end OAI

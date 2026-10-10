import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace HardSphere.Comparison
variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A]
lemma uniform_match_integral (G : ℝ) (x : A) :
    (∫y, (if x=y then G else 1) ∂(PMF.uniformOfFintype A).toMeasure)=
      1+(G-1)/(Fintype.card A:ℝ) := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  rw [←Finset.mul_sum]
  have h : (∑y:A,if x=y then G else (1:ℝ))=G+((Fintype.card A:ℝ)-1) := by
    have he (y : A) : (if x=y then G else (1:ℝ))=1+(if x=y then G-1 else 0) := by
      by_cases hxy : x=y <;> simp [hxy]
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_ite_eq]
    simp
    ring
  rw [h]
  have hn : (Fintype.card A:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring
lemma uniform_pair_match_integral (G : ℝ) :
    (∫p:A×A, (if p.1=p.2 then G else 1)
      ∂((PMF.uniformOfFintype A).toMeasure.prod (PMF.uniformOfFintype A).toMeasure))=
      1+(G-1)/(Fintype.card A:ℝ) := by
  rw [integral_prod _ (by exact Integrable.of_finite)]
  simp only [uniform_match_integral]
  simp

lemma prod_match_eq_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι→Type*} [∀i,DecidableEq (A i)] (G : ℝ) (p : ∀i,A i×A i) :
    (∏i,if (p i).1=(p i).2 then G else 1)=
      G^(Finset.univ.filter (fun i ↦ (p i).1=(p i).2)).card := by
  classical
  rw [Finset.prod_ite]
  simp

lemma label_match_moment {ι : Type*} [Fintype ι]
    (A : ι→Type*) [∀i,Fintype (A i)] [∀i,Nonempty (A i)] [∀i,DecidableEq (A i)]
    [∀i,MeasurableSpace (A i)] [∀i,MeasurableSingletonClass (A i)] (G M : ℝ)
    (hG : 1≤G) (hM : 0<M) (hcard : ∀i,M≤2*(Fintype.card (A i):ℝ)) :
    (∫p:∀i,A i×A i, ∏i,if (p i).1=(p i).2 then G else 1
      ∂Measure.pi (fun i ↦ (PMF.uniformOfFintype (A i)).toMeasure.prod
        (PMF.uniformOfFintype (A i)).toMeasure))≤
      Real.exp ((2*(G-1)/M)*(Fintype.card ι:ℝ)) := by
  rw [integral_fintype_prod_eq_prod (fun (i:ι) (p:A i×A i) ↦ if p.1=p.2 then G else 1)]
  simp only [uniform_pair_match_integral]
  calc
    _ ≤ ∏_i:ι,Real.exp (2*(G-1)/M) := by
      apply Finset.prod_le_prod₀
      · intro i _
        have := div_nonneg (sub_nonneg.mpr hG) (Nat.cast_nonneg (Fintype.card (A i)))
        linarith
      · intro i _
        have hn : (0:ℝ)<Fintype.card (A i) := by exact_mod_cast Fintype.card_pos
        have hd : (G-1)/(Fintype.card (A i):ℝ)≤2*(G-1)/M := by
          apply (div_le_div_iff₀ hn hM).mpr
          nlinarith [hcard i]
        linarith [Real.add_one_le_exp (2*(G-1)/M)]
    _ = _ := by rw [←Real.exp_sum];simp [mul_comm]

end HardSphere.Comparison

end
end

end

end OAI

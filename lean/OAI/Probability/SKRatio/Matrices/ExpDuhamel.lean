import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
namespace SKRatioGaussian
section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]

lemma exp_duhamel (a b : A) :
    exp a - exp b = ∫ u : ℝ in (0 : ℝ)..1, exp ((1-u) • a) * (a-b) * exp (u • b) := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => exp ((1-u) • a) * exp (u • b))
      (-(exp ((1-u) • a) * (a-b) * exp (u • b))) u := by
    have h₁ := (hasDerivAt_exp_smul_const a (1-u)).scomp u ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u))
    have h₂ := hasDerivAt_exp_smul_const' b u
    convert h₁.mul h₂ using 1 <;> (try simp only [zero_sub, neg_smul, one_smul]) <;> noncomm_ring
  have hc : Continuous (fun u : ℝ => -(exp ((1-u) • a) * (a-b) * exp (u • b))) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hc.intervalIntegrable 0 1)
  simpa only [intervalIntegral.integral_neg, sub_self, zero_smul, NormedSpace.exp_zero, one_mul,
    sub_zero, one_smul, mul_one, neg_neg, neg_sub] using congrArg Neg.neg hh.symm

end Algebra

section CStar
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedAlgebra ℚ A] [CompleteSpace A]
  [StarRing A] [ContinuousStar A] [CStarRing A]

omit [CStarRing A] in
lemma exp_skew_unitary (a : A) (ha : star a = -a) (t : ℝ)
    [StarModule ℝ A] : exp (t • a) ∈ unitary A := by
  apply exp_mem_unitary_of_mem_skewAdjoint
  change star (t • a) = -(t • a)
  simp [ha]

lemma exp_skew_difference [StarModule ℝ A] (a b : A)
    (ha : star a = -a) (hb : star b = -b) : ‖exp a - exp b‖ ≤ ‖a-b‖ := by
  rw [exp_duhamel]
  have hc : Continuous (fun u : ℝ => exp ((1-u) • a) * (a-b) * exp (u • b)) := by fun_prop
  have hh : ∀ u : ℝ, ‖exp ((1-u) • a) * (a-b) * exp (u • b)‖ = ‖a-b‖ := by
    intro u
    rw [CStarRing.norm_mul_coe_unitary _ ⟨_,exp_skew_unitary b hb u⟩,
      CStarRing.norm_coe_unitary_mul ⟨_,exp_skew_unitary a ha (1-u)⟩]
  calc
    ‖∫ u : ℝ in (0 : ℝ)..1, exp ((1-u) • a) * (a-b) * exp (u • b)‖ ≤
        ∫ u : ℝ in (0 : ℝ)..1, ‖exp ((1-u) • a) * (a-b) * exp (u • b)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = ‖a-b‖ := by simp only [hh]; simp

end CStar
end SKRatioGaussian

noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius

end
end
end
end
end
end
end
end
end

end OAI

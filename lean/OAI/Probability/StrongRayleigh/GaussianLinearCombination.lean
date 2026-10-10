import Mathlib

namespace OAI

universe u_1 u_2 u_3

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem336AdditiveD139.GaussianLinearCombination

variable {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

theorem hasLaw_finset_sum {X : I → Ω → ℝ} {m : I → ℝ} {v : I → ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) P)
    (hInd : iIndepFun X P) (s : Finset I) :
    HasLaw (fun ω => ∑ i ∈ s, X i ω)
      (gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i)) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      constructor
      · simp only [Finset.sum_empty]
        exact aemeasurable_const
      · simp
  | @insert i s hi ih =>
      have hsum : (∑ j ∈ s, X j) = (fun ω => ∑ j ∈ s, X j ω) := by
        funext ω
        simp only [Finset.sum_apply]
      have hind : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) P := by
        rw [← hsum]
        exact (hInd.indepFun_finsetSum_of_notMem₀
          (fun j => (hX j).aemeasurable) hi).symm
      constructor
      · simp only [Finset.sum_insert hi]
        exact (hX i).aemeasurable.add ih.aemeasurable
      · simpa only [Finset.sum_insert hi, Pi.add_def] using
          gaussianReal_add_gaussianReal_of_indepFun hind (hX i) ih

theorem hasLaw_finset_linearCombination {X : I → Ω → ℝ}
    {m : I → ℝ} {v : I → ℝ≥0}
    (hX : ∀ i, HasLaw (X i) (gaussianReal (m i) (v i)) P)
    (hInd : iIndepFun X P) (s : Finset I) (θ : I → ℝ) :
    HasLaw (fun ω => ∑ i ∈ s, θ i * X i ω)
      (gaussianReal (∑ i ∈ s, θ i * m i)
        (∑ i ∈ s, NNReal.mk (θ i ^ 2) (sq_nonneg (θ i)) * v i)) P := by
  apply hasLaw_finset_sum
  · intro i
    exact gaussianReal_const_mul (hX i) (θ i)
  · exact hInd.comp (fun i x => θ i * x) (fun i => measurable_const.mul measurable_id)

theorem hasLaw_centered_linearCombination {X : I → Ω → ℝ} (h : ℝ≥0)
    (hX : ∀ i, HasLaw (X i) (gaussianReal 0 h) P)
    (hInd : iIndepFun X P) (s : Finset I) (θ : I → ℝ) :
    HasLaw (fun ω => ∑ i ∈ s, θ i * X i ω)
      (gaussianReal 0 (h * ∑ i ∈ s, NNReal.mk (θ i ^ 2) (sq_nonneg (θ i)))) P := by
  simpa only [mul_zero, Finset.sum_const_zero, Finset.mul_sum, Finset.sum_mul, mul_comm h] using
    hasLaw_finset_linearCombination hX hInd s θ

omit [IsProbabilityMeasure P] in

theorem indepFun_linearCombination {E : Type u_3} [MeasurableSpace E]
    {X : I → Ω → ℝ} {H : Ω → E}
    (hPast : IndepFun (fun ω i => X i ω) H P)
    (s : Finset I) (θ : I → ℝ) :
    IndepFun (fun ω => ∑ i ∈ s, θ i * X i ω) H P := by
  exact hPast.comp (show Measurable (fun x : I → ℝ => ∑ i ∈ s, θ i * x i) by
    fun_prop) measurable_id

theorem hasLaw_brownian_linearCombination {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hInd : iIndepFun (fun i ω t => B i t ω) P)
    (s : Finset I) (θ : I → ℝ) (u v : ℝ≥0) :
    HasLaw (fun ω => ∑ i ∈ s, θ i * (B i v ω - B i u ω))
      (gaussianReal 0
        (nndist (v : ℝ) (u : ℝ) *
          ∑ i ∈ s, NNReal.mk (θ i ^ 2) (sq_nonneg (θ i)))) P := by
  apply hasLaw_centered_linearCombination
  · intro i
    exact (hB i).hasLaw_sub v u
  · exact hInd.comp (fun _ x => x v - x u) (fun _ => by fun_prop)

theorem hasLaw_brownian_linearCombination_of_le {B : I → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hInd : iIndepFun (fun i ω t => B i t ω) P)
    (s : Finset I) (θ : I → ℝ) {u v : ℝ≥0} (huv : u ≤ v) :
    HasLaw (fun ω => ∑ i ∈ s, θ i * (B i v ω - B i u ω))
      (gaussianReal 0
        ((v - u) * ∑ i ∈ s, NNReal.mk (θ i ^ 2) (sq_nonneg (θ i)))) P := by
  have hd : nndist (v : ℝ) (u : ℝ) = v - u := by
    apply NNReal.coe_injective
    simp only [coe_nndist, Real.dist_eq, NNReal.coe_sub huv]
    exact abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr huv))
  simpa only [hd] using hasLaw_brownian_linearCombination hB hInd s θ u v

end Problem336AdditiveD139.GaussianLinearCombination

end

end OAI

import OAI.Combinatorics.SharpThreshold.FourierBasis

namespace OAI

universe u

noncomputable section
open scoped BigOperators

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

lemma sqrt_variance_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) : 0 < Real.sqrt (p * (1 - p)) :=
  Real.sqrt_pos.2 (mul_pos hp (sub_pos.2 hp1))

lemma sqrt_variance_sq {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Real.sqrt (p * (1 - p)) ^ 2 = p * (1 - p) :=
  Real.sq_sqrt (mul_nonneg hp (sub_nonneg.2 hp1))

@[simp] lemma scalarWeight_sum (p : ℝ) : ∑ b : Bool, scalarWeight p b = 1 := by
  simp [scalarWeight]

@[simp] lemma chi_mean (p : ℝ) :
    ∑ b : Bool, scalarWeight p b * chi p b = 0 := by
  simp only [Fintype.sum_bool, scalarWeight, chi, ite_true,
    Bool.false_eq_true, ite_false]
  ring

lemma chi_second_moment {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∑ b : Bool, scalarWeight p b * (chi p b) ^ 2 = 1 := by
  have hs : Real.sqrt (p * (1 - p)) ≠ 0 := ne_of_gt (sqrt_variance_pos hp hp1)
  have hsq := sqrt_variance_sq (le_of_lt hp) (le_of_lt hp1)
  simp only [Fintype.sum_bool, scalarWeight, chi, ite_true,
    Bool.false_eq_true, ite_false]
  field_simp
  nlinarith

lemma expectation_product (p : ℝ) (g : ι → Bool → ℝ) :
    (∑ x : ι → Bool, weight p x * ∏ i, g i (x i)) =
      ∏ i, ∑ b : Bool, scalarWeight p b * g i b := by
  classical
  simpa only [weight, Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun i b => scalarWeight p b * g i b)).symm

lemma char_eq_univ_prod (p : ℝ) (S : Finset ι) (x : ι → Bool) :
    char p S x = ∏ i, if i ∈ S then chi p (x i) else 1 := by
  classical
  simp [char, Finset.prod_ite_mem]

lemma char_inner_product {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (S T : Finset ι) :
    (∑ x : ι → Bool, weight p x * char p S x * char p T x) =
      if S = T then 1 else 0 := by
  classical
  have hfactor :
      (∑ x : ι → Bool, weight p x * char p S x * char p T x) =
        ∏ i, ∑ b : Bool, scalarWeight p b *
          ((if i ∈ S then chi p b else 1) *
           (if i ∈ T then chi p b else 1)) := by
    simpa only [char_eq_univ_prod, Finset.prod_mul_distrib, mul_assoc] using
      expectation_product p (fun i b =>
        (if i ∈ S then chi p b else 1) *
        (if i ∈ T then chi p b else 1))
  rw [hfactor]
  by_cases hST : S = T
  · subst T
    simp only [ite_true]
    apply Finset.prod_eq_one
    intro i hi
    by_cases hiS : i ∈ S
    · simpa only [hiS, ite_true, ← pow_two] using chi_second_moment hp hp1
    · simpa only [hiS, ite_false, mul_one] using scalarWeight_sum p
  · simp only [hST, ite_false]
    obtain ⟨i, hi⟩ := not_forall.mp (Finset.ext_iff.not.mp hST)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hiS : i ∈ S
    · have hiT : i ∉ T := by tauto
      simpa only [hiS, hiT, ite_true, ite_false, mul_one, one_mul] using chi_mean p
    · have hiT : i ∈ T := by tauto
      simpa only [hiS, hiT, ite_true, ite_false, mul_one, one_mul] using chi_mean p

end Problem313.BiasedFourier

end

end OAI

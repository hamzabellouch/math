import OAI.Analysis.FreeEntropy.GUEConcentration

namespace OAI

universe u1 u2 u3

noncomputable section
open MeasureTheory ProbabilityTheory Finset Filter
open scoped Topology
namespace FiniteEntropySeparation
 theorem norm_sum_sq_le_card {ι : Type u1} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖^2 ≤ (s.card:ℝ) * ∑ i ∈ s, ‖f i‖^2 := by
  calc
    _ ≤ (∑ i ∈ s, ‖f i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖f i‖))
 theorem polynomial_sum_L2_tendsto {I : ℕ → Type} [∀ k,Fintype (I k)] [∀ k,DecidableEq (I k)]
    {α : Type u2} (s : Finset α) (F : (k:ℕ) → α → (I k → ℝ) → ℂ)
    (hF : ∀ k a,IsComplexPolynomial (F k a))
    (hlim : ∀ a ∈ s,Tendsto (fun k => ∫ x, ‖F k a x‖^2 ∂productGaussian (I k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖∑ a ∈ s,F k a x‖^2 ∂productGaussian (I k)) atTop (𝓝 0) := by
  apply squeeze_zero (fun k => integral_nonneg (fun _ => sq_nonneg _))
    (fun k => ?_) (by simpa using (tendsto_finsetSum s hlim).const_mul (s.card:ℝ))
  rw [← integral_finsetSum s (fun a _ => (hF k a).norm_sq.integrable),← integral_const_mul]
  apply integral_mono ((IsComplexPolynomial.finset_sum s (fun a _ => hF k a)).norm_sq.integrable)
    ((integrable_finsetSum s (fun a _ => (hF k a).norm_sq.integrable)).const_mul _)
  intro x
  exact norm_sum_sq_le_card s _
 theorem polynomial_const_mul_L2_tendsto {I : ℕ → Type} [∀ k,Fintype (I k)] [∀ k,DecidableEq (I k)]
    (F : (k:ℕ) → (I k → ℝ) → ℂ) (c : ℂ)
    (hlim : Tendsto (fun k => ∫ x, ‖F k x‖^2 ∂productGaussian (I k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, ‖c*F k x‖^2 ∂productGaussian (I k)) atTop (𝓝 0) := by
  simp only [norm_mul,mul_pow,integral_const_mul]
  simpa using hlim.const_mul (‖c‖^2)
namespace FreeSeries
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] [Fintype β] [DecidableEq β] in
theorem reparam_polynomial [DecidableEq α] [Fintype β] [DecidableEq β] {ι : Type u3} [Fintype ι] [DecidableEq ι]
    (c : α → β → ℂ) (F : (ι → ℝ) → Series α) (hF : ∀ w,IsComplexPolynomial (fun x => F x w))
    (w : List β) : IsComplexPolynomial (fun x => reparam c (F x) w) := by
  induction w generalizing F with
  | nil => exact hF []
  | cons b w ih =>
    exact IsComplexPolynomial.finset_sum univ (fun a _ => (ih (fun x => deriv a (F x)) (fun v => hF (a::v))).const_mul (c a b))
 theorem reparam_L2_tendsto {I : ℕ → Type} [∀ k,Fintype (I k)] [∀ k,DecidableEq (I k)]
    (c : α → β → ℂ) (F : (k:ℕ) → (I k → ℝ) → Series α) (M : Series α)
    (hF : ∀ k w,IsComplexPolynomial (fun x => F k x w))
    (hlim : ∀ w,Tendsto (fun k => ∫ x, ‖F k x w-M w‖^2 ∂productGaussian (I k)) atTop (𝓝 0))
    (w : List β) :
    Tendsto (fun k => ∫ x, ‖reparam c (F k x) w-reparam c M w‖^2 ∂productGaussian (I k)) atTop (𝓝 0) := by
  induction w generalizing F M with
  | nil => exact hlim []
  | cons b w ih =>
    simp only [reparam_cons,← Finset.sum_sub_distrib,← mul_sub]
    apply polynomial_sum_L2_tendsto
    · intro k a
      exact ((reparam_polynomial c (fun x => deriv a (F k x)) (fun v => hF k (a::v)) w).sub (IsComplexPolynomial.const _)).const_mul _
    · intro a _
      apply polynomial_const_mul_L2_tendsto
      exact ih (fun k x => deriv a (F k x)) (deriv a M) (fun k v => hF k (a::v)) (fun v => hlim (a::v))
end FreeSeries
end FiniteEntropySeparation

end

end OAI

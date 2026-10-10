import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers
import OAI.NumberTheory.CubicGram.Mobius

namespace OAI

/-! The manuscript's exact prime detector on a fixed norm envelope.
The finite weighted identity applies to both squarefree-supported kernels,
with the same coefficients before any estimate is used. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eventually_prime_detector_window {c C : ℝ} (hc : 0 < c) (_hC : 0 < C) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X^(2/5:ℝ) ∧
      ∀ n : Eisenstein, c*X ≤ norm n → norm n ≤ C*X →
        2*X^(2/5:ℝ) < norm n ∧ norm n < (X^(2/5:ℝ))^3 := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_rpow_le_const_mul (by norm_num : (2/5:ℝ) < 1) (show 0 < c/4 by positivity),
    eventually_const_mul_rpow_le (by norm_num : (1:ℝ) < 6/5) (2*C)] with X hX hlo hhi
  have hXp : 0 < X := zero_lt_one.trans hX
  have hz : 0 < X^(2/5:ℝ) := Real.rpow_pos_of_pos hXp _
  rw [Real.rpow_one] at hlo hhi
  have hcube : (X^(2/5:ℝ))^3 = X^(6/5:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hXp.le]
    norm_num
  refine ⟨Real.one_le_rpow hX.le (by norm_num : (0:ℝ) ≤ 2/5),?_⟩
  intro n hnlo hnhi
  constructor
  · nlinarith
  · rw [hcube]
    nlinarith

lemma squarefree_kernel_prime_detector {ψ : ℝ → ℝ} {z : ℝ}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) (hz : 1 ≤ z)
    {n : Eisenstein} (hlo : 2*z < norm n) (hhi : norm n < z^3)
    (K : Eisenstein → ℂ) (hK : ¬Squarefree n → K n = 0) :
    (if Prime n then K n else 0) =
      (roughProduct ψ z n:ℂ)*K n -
        (if (primeFactors n).card = 2 then (roughProduct ψ z n:ℂ)*K n else 0) := by
  by_cases hs : Squarefree n
  · have he := exact_prime_detector hψone hψzero hz hs hlo hhi
    have he' := congrArg (fun r : ℝ => (r:ℂ)*K n) he
    by_cases hp : Prime n <;> by_cases ht : (primeFactors n).card = 2 <;>
      simp only [hp,ht,ite_true,ite_false,Complex.ofReal_zero,Complex.ofReal_one,
        Complex.ofReal_sub,one_mul,zero_mul,sub_mul] at he' ⊢ <;> exact he'
  · have hp : ¬Prime n := fun hp => hs hp.squarefree
    simp [hp,hK hs]

/-- Exact finite prime sum decomposition on an arbitrary fixed envelope.
No analytic estimate and no kernel-specific coefficient is introduced. -/
theorem prime_detector_finite_envelope {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    {ψ : ℝ → ℝ}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) :
    ∀ᶠ X : ℝ in atTop, ∀ (S : Finset Eisenstein) (K : Eisenstein → ℂ),
      (∀ n ∈ S, c*X ≤ norm n ∧ norm n ≤ C*X) →
      (∀ n ∈ S, ¬Squarefree n → K n = 0) →
      (∑ n ∈ S with Prime n, K n) =
        (∑ n ∈ S, (roughProduct ψ (X^(2/5:ℝ)) n:ℂ)*K n) -
          ∑ n ∈ S with (primeFactors n).card = 2,
            (roughProduct ψ (X^(2/5:ℝ)) n:ℂ)*K n := by
  filter_upwards [eventually_prime_detector_window hc hC] with X hX
  intro S K hS hK
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact squarefree_kernel_prime_detector hψone hψzero hX.1
    (hX.2 n (hS n hn).1 (hS n hn).2).1
    (hX.2 n (hS n hn).1 (hS n hn).2).2 K (hK n hn)

end CubicFirstMoment

end

end OAI

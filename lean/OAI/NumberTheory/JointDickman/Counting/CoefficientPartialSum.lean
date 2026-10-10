import OAI.NumberTheory.JointDickman.Amplification.MultiplicativeExponentialInput

namespace OAI

/-! # Additive partial sums of the actual rough coefficient -/

namespace JointDickman
open Finset

noncomputable def coefficientAdditivePartialSum (B Y : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 Y, (coefficientWeight B n : ℂ)*additivePhase ((n : ℝ)*θ)

theorem coefficientAdditivePartialSum_factor (B Y : ℕ) (θ : ℝ) :
    coefficientAdditivePartialSum B Y θ = (coefficientScale B : ℂ)*
      ∑ n ∈ Icc 1 Y,
        (roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1/2) n : ℂ)*
          additivePhase ((n : ℝ)*θ) := by
  simp only [coefficientAdditivePartialSum,coefficientWeight,Complex.ofReal_mul,mul_sum]
  apply sum_congr rfl
  intro n _
  ring

theorem coefficient_additive_partial_sum_bound
    (hMV : PublishedInputs.MultiplicativeExponentialInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B Y q : ℕ) (u : ℤ) (θ R : ℝ),
    2 ≤ Y → 0 < q → Nat.Coprime u.natAbs q →
    |θ-(u : ℝ)/q| ≤ 1/(q : ℝ)^2 →
    2 ≤ R → R ≤ q → (q : ℝ) ≤ Y/R →
    ‖coefficientAdditivePartialSum B Y θ‖ ≤
      C*coefficientScale B*((Y : ℝ)/Real.log Y + Y*(Real.log R)^(3/2 : ℝ)/Real.sqrt R) := by
  obtain ⟨C,hC,hbound⟩ := rough_exponential_partial_sum_bound hMV
  refine ⟨C,hC,?_⟩
  intro B Y q u θ R hY hq hcop happ hR hRq hqY
  rw [coefficientAdditivePartialSum_factor,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (coefficientScale_nonneg B)]
  exact (mul_le_mul_of_nonneg_left
    (hbound _ Y q u θ R hY hq hcop happ hR hRq hqY) (coefficientScale_nonneg B)).trans_eq
      (by ring)

end JointDickman

end OAI

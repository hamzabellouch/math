import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeRetainedSum

namespace OAI

/-! Finite amplitude reconstruction preserves a restricted pairing bound
with precisely the product of its two amplitude-weight sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_amplitude_matrix_bound (I J : Finset ℤ) (m n : ℤ → ℝ)
    (pairing : ℤ → ℤ → ℂ) (C : ℝ)
    (hpair : ∀ i∈I, ∀ j∈J, ‖pairing i j‖≤C*Real.sqrt (m i)*Real.sqrt (n j)) :
    ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • pairing i j‖≤
      C*(∑ i∈I, (2:ℝ)^i*Real.sqrt (m i))*(∑ j∈J, (2:ℝ)^j*Real.sqrt (n j)) := by
  calc
    _≤∑ i∈I, ∑ j∈J, ‖((2:ℝ)^i*(2:ℝ)^j) • pairing i j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _≤∑ i∈I, ∑ j∈J, C*((2:ℝ)^i*Real.sqrt (m i))*((2:ℝ)^j*Real.sqrt (n j)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_smul,Real.norm_of_nonneg (by positivity : 0≤(2:ℝ)^i*(2:ℝ)^j)]
      calc
        _≤((2:ℝ)^i*(2:ℝ)^j)*(C*Real.sqrt (m i)*Real.sqrt (n j)) :=
          mul_le_mul_of_nonneg_left (hpair i hi j hj) (by positivity)
        _=_ := by ring
    _=(∑ i∈I, C*((2:ℝ)^i*Real.sqrt (m i)))*
        (∑ j∈J, (2:ℝ)^j*Real.sqrt (n j)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _=_ := congrArg (fun x : ℝ => x*(∑ j∈J, (2:ℝ)^j*Real.sqrt (n j)))
      (Finset.mul_sum I (fun i => (2:ℝ)^i*Real.sqrt (m i)) C).symm

theorem amplitude_weight_sum_unnormalize (I : Finset ℤ) (m : ℤ → ℝ)
    (M : ℝ) (hM : 0<M) (hm : ∀ i∈I, 0≤m i) :
    (∑ i∈I, (2:ℝ)^i*Real.sqrt (m i))=
      (∑ i∈I, (2:ℝ)^i*Real.sqrt (m i/M))*Real.sqrt M := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.sqrt_div (hm i hi), mul_assoc,div_mul_cancel₀ _ (Real.sqrt_pos.2 hM).ne']

end LipschitzHilbert

end

end OAI

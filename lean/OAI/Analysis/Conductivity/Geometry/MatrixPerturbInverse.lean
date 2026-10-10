import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

variable {ι P : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace P]

omit [DecidableEq ι] in
lemma matrix_pi_mulVec_bound (A : Matrix ι ι ℝ) (b : ι → ℝ) (i : ι) :
    ‖(A*ᵥb) i‖≤(Fintype.card ι:ℝ)*‖A‖*‖b‖ := by
  change ‖∑ j,A i j*b j‖≤_
  calc
    _≤∑ j,‖A i j*b j‖ := norm_sum_le _ _
    _≤∑ j,‖A‖*‖b‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i))
        (norm_le_pi_norm b j) (norm_nonneg _) (norm_nonneg _)
    _=_ := by simp [mul_assoc]

theorem matrix_inverse_locally_bounded {M : P → Matrix ι ι ℝ} {p₀ : P}
    (hM : ContinuousAt M p₀) (h₀ : IsUnit (M p₀)) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ p in 𝓝 p₀,
      IsUnit (M p) ∧ (∀ b : ι → ℝ,
        M p*ᵥ((M p)⁻¹*ᵥb)=b ∧ ∀ i,‖((M p)⁻¹*ᵥb) i‖≤C*‖b‖) := by
  have hd₀ : (M p₀).det≠0 := isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp h₀)
  have hdi : ContinuousAt Ring.inverse (M p₀).det := by
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hd₀)
  have hi : ContinuousAt (fun p => (M p)⁻¹) p₀ :=
    (continuousAt_matrix_inv _ hdi).comp hM
  have hn : ∀ᶠ p in 𝓝 p₀,‖(M p)⁻¹‖<‖(M p₀)⁻¹‖+1 :=
    hi.norm.eventually (gt_mem_nhds (by linarith))
  have hd : ∀ᶠ p in 𝓝 p₀,(M p).det≠0 :=
    ((continuous_id.matrix_det).continuousAt.comp hM).tendsto.eventually (isOpen_ne.mem_nhds hd₀)
  let C := ((Fintype.card ι:ℝ)+1)*(‖(M p₀)⁻¹‖+1)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hn,hd] with p hp hpd
  have hu : IsUnit (M p).det := isUnit_iff_ne_zero.mpr hpd
  refine ⟨(isUnit_iff_isUnit_det _).mpr hu,?_⟩
  intro b
  refine ⟨?_,?_⟩
  · rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec]
  · intro i
    apply (matrix_pi_mulVec_bound _ b i).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg b)
    have hn₀ : 0≤‖(M p₀)⁻¹‖+1 := by positivity
    dsimp only [C]
    have hh := mul_le_mul_of_nonneg_left hp.le (show (0:ℝ)≤Fintype.card ι by positivity)
    nlinarith

end ScalarConductivity

end

end OAI

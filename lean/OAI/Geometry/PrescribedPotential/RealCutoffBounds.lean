import Mathlib
import OAI.Geometry.PrescribedPotential.RealFrameScalar

namespace OAI

/-! Real Cutoff Bounds. -/

section

 
noncomputable section
open Set Filter Topology Finset
open scoped ContDiff
namespace HigherJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma frameGradient_const_mul {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (v : ι → E) (c : ℝ) : frameGradient v (fun y => c*f y) x = c • frameGradient v f x := by
  rw [frameGradient_mul (differentiableAt_const c) hf,frameGradient_const]
  simp

lemma frameGradient_square {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (v : ι → E) :
    ‖frameGradient v (fun y => (f y)^2) x‖^2 = 4*(f x)^2*‖frameGradient v f x‖^2 := by
  have he : (fun y => (f y)^2) = (fun y => f y*f y) := by funext y; ring
  rw [he,frameGradient_mul hf hf,← add_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring

lemma cutoff_uniform_frames {K : Set E} (hK : IsCompact K) (χ : E → ℝ)
    (hχ : ContDiff ℝ ∞ χ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ v : ι → E, (∀ i, ‖v i‖ ≤ B) →
      -C ≤ frameLaplace v (fun y => (χ y)^2) x ∧
      ‖frameGradient v (fun y => (χ y)^2) x‖^2 ≤ C*(χ x)^2 := by
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn (hχ.fderiv_right (m := ∞) (by simp)).continuous.continuousOn
  obtain ⟨H,hH⟩ := hK.exists_bound_of_continuousOn
    (((hχ.pow 2).fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuous.continuousOn
  let D' := max D 0
  let H' := max H 0
  let C := (Fintype.card ι : ℝ)*H'*B^2 + 4*(Fintype.card ι : ℝ)*D'^2*B^2
  have hD' : 0 ≤ D' := le_max_right _ _
  have hH' : 0 ≤ H' := le_max_right _ _
  have hC1 : (Fintype.card ι : ℝ)*H'*B^2 ≤ C := le_add_of_nonneg_right (by positivity)
  have hC2 : 4*(Fintype.card ι : ℝ)*D'^2*B^2 ≤ C := le_add_of_nonneg_left (by positivity)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro x hx v hv
  have hd : ‖fderiv ℝ χ x‖ ≤ D' := (hD x hx).trans (le_max_left _ _)
  have hh : ‖fderiv ℝ (fderiv ℝ (fun y => (χ y)^2)) x‖ ≤ H' := (hH x hx).trans (le_max_left _ _)
  have hgrad : ‖frameGradient v χ x‖^2 ≤ (Fintype.card ι : ℝ)*D'^2*B^2 := by
    rw [norm_frameGradient_sq]
    calc
      _ ≤ ∑ _i : ι, (D'*B)^2 := by
        apply sum_le_sum
        intro i _
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact ((fderiv ℝ χ x).le_opNorm _).trans (mul_le_mul hd (hv i) (norm_nonneg _) hD')
      _ = _ := by simp; ring
  constructor
  · have hl : ‖frameLaplace v (fun y => (χ y)^2) x‖ ≤ (Fintype.card ι : ℝ)*H'*B^2 := by
      unfold frameLaplace
      calc
        _ ≤ ∑ i, ‖dir (v i) (dir (v i) (fun y => (χ y)^2)) x‖ := norm_sum_le _ _
        _ ≤ ∑ _i : ι, H'*B^2 := by
          apply sum_le_sum
          intro i _
          rw [dir_dir (hχ.contDiffAt.pow 2)]
          exact (((fderiv ℝ (fderiv ℝ (fun y => (χ y)^2)) x) (v i)).le_opNorm _).trans
            ((mul_le_mul
              (((fderiv ℝ (fderiv ℝ (fun y => (χ y)^2)) x).le_opNorm _).trans
                (mul_le_mul hh (hv i) (norm_nonneg _) hH')) (hv i) (norm_nonneg _) (by positivity)).trans_eq (by ring))
        _ = _ := by simp; ring
    exact (neg_le_neg (hl.trans hC1)).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le (frameLaplace v (fun y => (χ y)^2) x))
  · rw [frameGradient_square (hχ.differentiable (by simp) x)]
    have hm := mul_le_mul_of_nonneg_left hgrad (show 0 ≤ 4*(χ x)^2 by positivity)
    have hn := mul_le_mul_of_nonneg_right hC2 (sq_nonneg (χ x))
    nlinarith only [hm,hn]
end HigherJet

end
end

end OAI

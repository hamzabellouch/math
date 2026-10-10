import Mathlib
import OAI.Probability.SKRatio.Quantization.BinStability
import OAI.Probability.SKRatio.Variational.ScalarHilbert

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open Bins Scalar SKRatioClock.Regression MatrixNet Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma fieldProjection_opNorm_le_one (hn : 0<n) : euclideanOpNorm (fieldProjection n) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ)≤1)
  intro x
  change ‖WithLp.toLp 2 (fieldProjection n *ᵥ x.ofLp)‖ ≤ 1*‖x‖
  rw [fieldProjection_mulVec,one_mul]
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hs := centered_sq_le x.ofLp
  rw [←EuclideanSpace.real_norm_sq_eq x] at hs
  have ht := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (centered x.ofLp))
  nlinarith only [hs,ht,norm_nonneg x,norm_nonneg (WithLp.toLp 2 (centered x.ofLp))]

lemma projected_opNorm_le (hn : 0<n) (M : Matrix (Fin n) (Fin n) ℝ) :
    euclideanOpNorm (fieldProjection n*M*fieldProjection n) ≤ euclideanOpNorm M := by
  unfold euclideanOpNorm
  rw [map_mul,map_mul]
  apply (norm_mul_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans
  have hp := fieldProjection_opNorm_le_one hn
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (fieldProjection n)‖ ≤ 1 at hp
  calc
    _ ≤ 1*‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖*1 := by gcongr
    _ = _ := by ring

lemma fullMean_opNorm_le (β : ℝ) :
    euclideanOpNorm (fun _ _ : Fin n => β^2/(n:ℝ)) ≤ β^2 := by
  apply matrix_opNorm_le_schur _ _ (sq_nonneg β)
  all_goals
    intro i
    have hn : 0<n := Nat.zero_lt_of_lt i.isLt
    rw [mean_constant_rows hn β i]

lemma centered_augmented_opNorm_le (β : ℝ) (g : (Fin n × Fin n) → ℝ)
    {D : ℝ} (hD : 0≤D) (hd : ∀ i, |augmentedDiagonal β g i|≤D) :
    euclideanOpNorm (β • goe g) ≤
      euclideanOpNorm (coupling (augmentedDisorder β g))+D+β^2 := by
  have he : β • goe g = Matrix.of (coupling (augmentedDisorder β g))+
      Matrix.diagonal (augmentedDiagonal β g) - Matrix.of (fun _ _ : Fin n => β^2/(n:ℝ)) := by
    ext i j
    have hc := congrFun (congrFun (coupling_augmentedDisorder β g) i) j
    change coupling (augmentedDisorder β g) i j = augmented β g i j-
      Matrix.diagonal (augmentedDiagonal β g) i j at hc
    change β*goe g i j = coupling (augmentedDisorder β g) i j+
      Matrix.diagonal (augmentedDiagonal β g) i j-β^2/(n:ℝ)
    rw [hc]
    change β*goe g i j = (β*goe g i j+β^2/(n:ℝ)-_)+_-β^2/(n:ℝ)
    ring
  unfold euclideanOpNorm
  rw [he,map_sub,map_add]
  apply (norm_sub_le _ _).trans
  exact (add_le_add (norm_add_le _ _) le_rfl).trans
    (add_le_add (add_le_add le_rfl (matrix_diagonal_opNorm_le _ D hD hd)) (fullMean_opNorm_le β))

theorem residual_norm_rare {β : ℝ} (hβ : 0<β) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | 2*β+2*β^2+2 <
        euclideanOpNorm (fieldProjection n*(β • goe g)*fieldProjection n)}) := by
  apply ((augmented_norm_rare hβ (by norm_num : (0:ℝ)<1)).union
    (augmented_diagonal_rare β (by norm_num : (0:ℝ)<1))).mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro g hg
  by_contra h
  have hnot := not_or.mp h
  have hnorm : euclideanOpNorm (coupling (augmentedDisorder β g)) ≤ 2*β+β^2+1 := not_lt.mp hnot.1
  have hdiag : ∀ i : Fin n, |augmentedDiagonal β g i| ≤ 1 := by
    intro i
    exact not_lt.mp (fun hi => hnot.2 ⟨i,hi⟩)
  have hr := (projected_opNorm_le hn (β • goe g)).trans
    (centered_augmented_opNorm_le β g (by norm_num) hdiag)
  change 2*β+2*β^2+2 < _ at hg
  linarith only [hg,hr,hnorm]

end SKRatio.Planted

end

end OAI

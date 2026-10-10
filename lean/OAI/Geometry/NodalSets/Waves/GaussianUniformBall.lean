import Mathlib.MeasureTheory.Measure.OpenPos
import OAI.Geometry.NodalSets.Waves.EuclideanGaussianSmallBall

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma stdGaussian_open_positive : (stdGaussian E).IsOpenPosMeasure := by
  let : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:NNReal) ≠ 0)).isOpenPosMeasure
  rw [← map_pi_eq_stdGaussian]
  apply Continuous.isOpenPosMeasure_map (by fun_prop)
  exact (WithLp.equiv 2 (ι → ℝ)).symm.surjective

lemma uniform_gaussian_ball (R r : ℝ) (hr : 0 < r) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ z : E, ‖z‖ ≤ R → p ≤ stdGaussian E (ball z r) := by
  classical
  let : (stdGaussian E).IsOpenPosMeasure := stdGaussian_open_positive
  obtain ⟨s,hs⟩ := (isCompact_closedBall (0:E) R).elim_finite_subcover
    (fun z : E ↦ ball z (r/2)) (fun _ ↦ isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨z,mem_ball_self (by positivity)⟩)
  let p : ℝ≥0∞ := s.inf (fun z ↦ stdGaussian E (ball z (r/2)))
  have hp : 0 < p := by
    dsimp only [p]
    clear hs p
    induction s using Finset.induction_on with
    | empty => simp
    | @insert z s hz ih =>
      rw [Finset.inf_insert]
      exact lt_min (measure_ball_pos _ _ (by positivity)) ih
  refine ⟨p,hp,?_⟩
  intro z hz
  have hz' : z ∈ closedBall (0:E) R := by simpa only [mem_closedBall,dist_zero_right] using hz
  obtain ⟨y,hy,hyz⟩ := mem_iUnion₂.mp (hs hz')
  apply (Finset.inf_le hy).trans
  apply measure_mono
  intro x hx
  have hx' : dist x y < r/2 := hx
  have hz'' : dist z y < r/2 := hyz
  have hh := dist_triangle x y z
  rw [dist_comm y z] at hh
  change dist x z < r
  linarith

lemma uniform_affine_gaussian_ball (A B M r : ℝ) (hA : 0 ≤ A)
    (hB : 0 < B) (hM : 0 ≤ M) (hr : 0 < r) (target : E) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ (L : E ≃L[ℝ] E) (mean : E),
      ‖L.symm.toContinuousLinearMap‖ ≤ A → ‖L.toContinuousLinearMap‖ ≤ B → ‖mean‖ ≤ M →
      p ≤ ((stdGaussian E).map (fun z ↦ mean+L z)) (ball target r) := by
  let radius : NNReal := ⟨A*(‖target‖+M), mul_nonneg hA (add_nonneg (norm_nonneg _) hM)⟩
  obtain ⟨p,hp,huniform⟩ := uniform_gaussian_ball (ι := ι) radius (r/B) (div_pos hr hB)
  refine ⟨p,hp,?_⟩
  intro L mean hLi hL hm
  let center := L.symm (target-mean)
  have hc : ‖center‖ ≤ A*(‖target‖+M) := by
    exact (L.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul hLi ((norm_sub_le _ _).trans (add_le_add le_rfl hm)) (norm_nonneg _) hA)
  apply (huniform center hc).trans
  rw [Measure.map_apply (by fun_prop) isOpen_ball.measurableSet]
  apply measure_mono
  intro z hz
  change dist (mean+L z) target < r
  rw [dist_eq_norm]
  have he : mean+L z-target = L (z-center) := by
    simp only [map_sub,center,L.apply_symm_apply]
    abel
  rw [he]
  have hb := L.toContinuousLinearMap.le_opNorm (z-center)
  have hh : ‖z-center‖ < r/B := by simpa only [mem_ball,dist_eq_norm] using hz
  have hmul := (lt_div_iff₀ hB).mp hh
  calc
    _ ≤ B*‖z-center‖ := hb.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
    _ < r := by nlinarith

end
end Yau.Probability

end OAI

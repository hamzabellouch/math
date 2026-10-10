import OAI.Geometry.TriangularCovering.Shadows
import OAI.Geometry.TriangularCovering.Asymptotics

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma small_abs_le_one {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ η/2) : |ε| ≤ 1 := by
  rw [abs_of_pos he]
  dsimp [η] at hsmall
  linarith only [hsmall]

/-- The area expansion with explicit uniform remainder constant 14. -/
theorem finiteFamily_expansion {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ η/2) :
    |totalArea (finiteFamily ε he)/H - (1/2-(13/6000:ℝ)*ε^2)| ≤ 14*ε^4 := by
  rw [finiteFamily_total]
  exact uniform_scalar_sum (small_abs_le_one he hsmall) (ceil_count_pos he) (ceil_step_le he)

lemma finiteFamily_ratio_lt {ε : ℝ} (he : 0 < ε) (hsmall : ε < η/2) :
    totalArea (finiteFamily ε he)/H < 1/2 := by
  have hr := (abs_le.mp (finiteFamily_expansion he hsmall.le)).2
  have hesq : ε^2 < (η/2)^2 := (sq_lt_sq₀ he.le (by norm_num [η])).2 hsmall
  have hc : 14*ε^2 < (13/6000:ℝ) := by norm_num [η] at hesq; linarith only [hesq]
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos he) (sub_neg.mpr hc)
  nlinarith only [hr,hneg]

lemma finiteFamily_strict {ε : ℝ} (he : 0 < ε) (hsmall : ε < η/2) :
    totalArea (finiteFamily ε he) < A_min/2 := by
  rw [projection_minimum]
  have h := (div_lt_iff₀ H_pos).mp (finiteFamily_ratio_lt he hsmall)
  linarith only [h]

/-- The asymptotic covering bound, including exact finite count and strict saving. -/
theorem main_asymptotic : MainAsymptotic := by
  refine ⟨η/2,14,by norm_num [η],by norm_num,?_⟩
  intro ε he hsmall
  exact ⟨finiteFamily ε he,finiteFamily_covers he hsmall.le,
    finiteFamily_expansion he hsmall.le,finiteFamily_strict he hsmall⟩

lemma relativeCost_le_totalArea {m : ℕ} (c : Fin m → TriCylinder) :
    relativeCost c ≤ totalArea c/H := by
  unfold relativeCost totalArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg H_pos
    (shadowArea_ge_H (c i).unit_axis)

/-- The normalized covering bound using perpendicular shadows. -/
theorem normalized_counterexample : NormalizedCounterexample := by
  have he : 0 < η/4 := by norm_num [η]
  have hs : η/4 < η/2 := by norm_num [η]
  refine ⟨2*n (η/4),finiteFamily (η/4) he,finiteFamily_covers he hs.le,?_⟩
  exact (relativeCost_le_totalArea _).trans_lt (finiteFamily_ratio_lt he hs)

/-- The minimum shadow area, asymptotic covering bound, and normalized counterexample. -/
theorem main : A_min = H ∧ MainAsymptotic ∧ NormalizedCounterexample :=
  ⟨projection_minimum,main_asymptotic,normalized_counterexample⟩

end TriangularCovering

end

end OAI

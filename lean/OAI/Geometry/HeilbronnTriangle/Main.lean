import OAI.Geometry.HeilbronnTriangle.Definitions
import OAI.Geometry.HeilbronnTriangle.Refutation
import OAI.Geometry.HeilbronnTriangle.ActualWeightedFiberCount

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

namespace Problem355

theorem heilbronn_power_lower_bound :
    0 < heilbronnExponent ∧ ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point, Filter.Tendsto n Filter.atTop Filter.atTop ∧ ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧ triangleAreasAtLeast (P j) (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  let Ct : ℝ := (128 / 7 : ℝ) * UniformFixedFiberCount.countConstant
  have hCt : 0 ≤ Ct :=
    mul_nonneg (by norm_num) UniformFixedFiberCount.countConstant_nonneg
  apply ParameterSampling.heilbronn_power_lower_bound_of_point_laws
    8 Ct (by norm_num) hCt
  refine ⟨0, ?_⟩
  intro r _ hr _ D
  let : Fact r.Prime := ⟨hr⟩
  let : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
  refine ⟨ActualPointLaw.pointLaw D, ActualPointLaw.pairProbability_le D, ?_⟩
  exact ActualPointLaw.tripleProbability_le_of_count D
    UniformFixedFiberCount.countConstant_nonneg
    (fun A => ActualPointLaw.weightedFiberBound_of_matrix_count
      UniformFixedFiberCount.countConstant
      @UniformFixedFiberCount.matrix_fiber_le D A)

theorem almost_n_minus_two_refuted :
    0 < heilbronnExponent / 2 ∧ ¬ eventualAlmostUpperBound (heilbronnExponent / 2) := by
  obtain ⟨hc, n, P, hn, hP⟩ := heilbronn_power_lower_bound
  exact ⟨by positivity,
    not_eventualAlmostUpperBound_of_sequence (by linarith) hn hP⟩

end Problem355

end

end OAI

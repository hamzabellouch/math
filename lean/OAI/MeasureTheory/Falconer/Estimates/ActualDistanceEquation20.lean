import OAI.MeasureTheory.Falconer.Graphs.WeightedDistanceCoincidence
import OAI.MeasureTheory.Falconer.Fourier.DistanceSincCollision

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem actual_weighted_distance_equation20 : ∃ C : ℝ, 0 < C ∧
    ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ], 0 < d.Q.side →
      d.StronglySeparated → d.ρ d.Q.carrierᶜ = 0 →
      d.coincidence.toReal ≤ C*(2:ℝ)^(-(d.a:ℝ)) *
        ∫ r in Icc (-((2:ℝ)^d.t)) ((2:ℝ)^d.t), ‖charFun d.weightedDistance r‖^2 := by
  obtain ⟨C,hC,hfourier⟩ := finite_measure_distance_collision_fourier
  refine ⟨2004*C,by positivity,?_⟩
  intro d _ hQ hs hcarry
  let := d.weightedDistance_isFinite hQ hs
  have hf := hfourier d.weightedDistance ((2:ℝ)^d.t) (by positivity)
  have hd := d.coincidence_le_weighted_collision hQ hs hcarry
  have hw : 100*d.width = 100/(2:ℝ)^d.t := by
    simp only [PositiveDistanceData.width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_natCast,div_eq_mul_inv]
  have hp : (2:ℝ)^((d.t:ℝ)-d.a) = (2:ℝ)^(-(d.a:ℝ)) * (2:ℝ)^d.t := by
    rw [← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  rw [hw,hp] at hd
  have h := mul_le_mul_of_nonneg_left hf (show 0 ≤ 2004*(2:ℝ)^(-(d.a:ℝ)) by positivity)
  calc
    _ ≤ (2004*(2:ℝ)^(-(d.a:ℝ))) *
        (((2:ℝ)^d.t)*(d.weightedDistance.prod d.weightedDistance).real
          {z : ℝ × ℝ | |z.1-z.2| ≤ 100/(2:ℝ)^d.t}) := by
      simpa only [mul_assoc] using hd
    _ ≤ _ := h
    _ = _ := by ring

theorem actual_source_distance_equation20 : ∃ C : ℝ, 0 < C ∧
    ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ], d.Q.side = 1 →
      d.X.length = d.a → d.Y.length = d.a → d.ρ d.Q.carrierᶜ = 0 →
      100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
      dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
      d.coincidence.toReal ≤ C*(2:ℝ)^(-(d.a:ℝ)) *
        ∫ r in Icc (-((2:ℝ)^d.t)) ((2:ℝ)^d.t), ‖charFun d.weightedDistance r‖^2 := by
  obtain ⟨C,hC,h⟩ := actual_weighted_distance_equation20
  refine ⟨C,hC,?_⟩
  intro d _ hQ hX hY hcarry hl hu
  exact h d (by rw [hQ]; norm_num) (d.stronglySeparated_of_unit hQ hX hY hl hu) hcarry

end PlanarFalconer

end OAI

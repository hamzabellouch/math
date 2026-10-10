import OAI.Geometry.CylinderCovering.Rational.RealizationDefinitions

namespace OAI

open Set
noncomputable section

namespace SlopeRational

private theorem physicalScale_sq : physicalScale ^ 2 = (1/2:ℝ) := by
  norm_num [physicalScale, div_pow, Real.sq_sqrt]

private theorem space_dist_sq (x y : Space) :
    dist x y ^ 2 = (x 0-y 0)^2 + (x 1-y 1)^2 + (x 2-y 2)^2 := by
  rw [dist_eq_norm, PiLp.norm_sq_eq_of_L2]
  simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  ring

theorem referenceTetrahedron_dist_le_one {x y : Space}
    (hx : x ∈ referenceTetrahedron) (hy : y ∈ referenceTetrahedron) :
    dist x y ≤ 1 := by
  obtain ⟨t,ht0,ht1,hx0,hx1,hx2⟩ := hx
  obtain ⟨s,hs0,hs1,hy0,hy1,hy2⟩ := hy
  have h0 : |x 0-y 0| ≤ (1+t+s)/2 := by
    calc
      |x 0-y 0| ≤ |x 0|+|y 0| := by simpa using abs_sub_le (x 0) 0 (y 0)
      _ ≤ (1+t+s)/2 := by linarith
  have h1 : |x 1-y 1| ≤ (1-t-s)/2 := by
    calc
      |x 1-y 1| ≤ |x 1|+|y 1| := by simpa using abs_sub_le (x 1) 0 (y 1)
      _ ≤ (1-t-s)/2 := by linarith
  have h0sq : (x 0-y 0)^2 ≤ ((1+t+s)/2)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by linarith : 0 ≤ (1+t+s)/2)).2 h0
  have h1sq : (x 1-y 1)^2 ≤ ((1-t-s)/2)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by linarith : 0 ≤ (1-t-s)/2)).2 h1
  have ht : t^2 ≤ (1/4:ℝ) := by nlinarith
  have hs : s^2 ≤ (1/4:ℝ) := by nlinarith
  have hz : (x 2-y 2)^2 = (1/2:ℝ)*(t-s)^2 := by
    rw [hx2,hy2,← mul_sub,mul_pow,physicalScale_sq]
  have hd := space_dist_sq x y
  rw [hz] at hd
  nlinarith [dist_nonneg (x := x) (y := y)]

theorem referenceTetrahedron_diameter : Metric.diam referenceTetrahedron = 1 := by
  apply le_antisymm
  · exact Metric.diam_le_of_forall_dist_le (by norm_num)
      (fun x hx y hy => referenceTetrahedron_dist_le_one hx hy)
  · let x : Space := RuledApproximation.vec3 (1/2) 0 (physicalScale/2)
    let y : Space := RuledApproximation.vec3 (-(1/2)) 0 (physicalScale/2)
    have hx : x ∈ referenceTetrahedron := by
      refine ⟨1/2,by norm_num,le_rfl,?_,?_,?_⟩
      · change |(1/2:ℝ)| ≤ (1/2+1/2)/2
        norm_num
      · change |(0:ℝ)| ≤ (1/2-1/2)/2
        norm_num
      · change physicalScale/2 = physicalScale*(1/2)
        ring
    have hy : y ∈ referenceTetrahedron := by
      refine ⟨1/2,by norm_num,le_rfl,?_,?_,?_⟩
      · change |(-(1/2):ℝ)| ≤ (1/2+1/2)/2
        norm_num
      · change |(0:ℝ)| ≤ (1/2-1/2)/2
        norm_num
      · change physicalScale/2 = physicalScale*(1/2)
        ring
    have hbounded : Bornology.IsBounded referenceTetrahedron :=
      Metric.isBounded_iff.2 ⟨1, fun x hx y hy => referenceTetrahedron_dist_le_one hx hy⟩
    have hdist : dist x y = 1 := by
      have h := space_dist_sq x y
      change dist x y ^ 2 = ((1/2:ℝ)-(-(1/2)))^2 + (0-0)^2 +
        (physicalScale/2-physicalScale/2)^2 at h
      norm_num at h
      rcases h with h | h
      · exact h
      · linarith [dist_nonneg (x := x) (y := y)]
    simpa only [hdist] using Metric.dist_le_diam_of_mem hbounded hx hy

end SlopeRational

end

end OAI

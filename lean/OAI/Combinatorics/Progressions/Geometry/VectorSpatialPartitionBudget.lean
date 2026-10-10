import OAI.Combinatorics.Progressions.Dynamics.VectorSiteBudget

namespace OAI

section

namespace Erdos3

theorem vectorSpatial_radius_inverse_budget (d : ℕ) {G C K ε P : ℝ}
    (hG0 : 0 ≤ G) (hC0 : 0 ≤ C) (hK0 : 0 ≤ K) (hε : 0 < ε) (hP : 0 ≤ P)
    (hG : G ≤ Real.exp P) (hC : C ≤ Real.exp P) (hK : K ≤ Real.exp P)
    (hεi : ε⁻¹ ≤ Real.exp P) :
    let S := (d + 1) * (2*P + 4) + d + 1
    1 / spatialSiteRadius G K (vectorSpatialAccuracy d (2 + G*C) ε) ≤ Real.exp (3*S + 16) := by
  have hGC : G*C ≤ Real.exp (2*P) := by
    calc
      _ ≤ Real.exp P * Real.exp P := mul_le_mul hG hC hC0 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have he : 1 ≤ Real.exp (2*P) := Real.one_le_exp_iff.mpr (by positivity)
  have hA : 2 + G*C ≤ Real.exp (2*P + 4) := by
    calc
      _ ≤ 3 * Real.exp (2*P) := by linarith
      _ ≤ Real.exp 4 * Real.exp (2*P) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith [Real.add_one_le_exp (4 : ℝ)]
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hP' : P ≤ 2*P + 4 := by linarith
  have hδ := vectorSpatialAccuracy_inverse_le_exp d (by positivity) hε hA
    (hεi.trans (Real.exp_le_exp.mpr hP'))
  have hS : P ≤ (d + 1 : ℝ) * (2*P + 4) + d + 1 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hS0 : 0 ≤ (d + 1 : ℝ) * (2*P + 4) + d + 1 := by positivity
  exact spatialSiteRadius_inverse_le_exp hG0 hK0
    (vectorSpatialAccuracy_pos d (by positivity) hε) hS0
    (hG.trans (Real.exp_le_exp.mpr hS)) (hK.trans (Real.exp_le_exp.mpr hS))
    (by simpa only [one_div] using hδ)

theorem vectorSpatial_partition_budget (d n : ℕ) {m G C K ε P : ℝ}
    (hm0 : 0 ≤ m) (hG0 : 0 ≤ G) (hC0 : 0 ≤ C) (hK0 : 0 ≤ K)
    (hε : 0 < ε) (hP : 0 ≤ P) (hm : m ≤ Real.exp P) (hG : G ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hK : K ≤ Real.exp P) (hεi : ε⁻¹ ≤ Real.exp P) :
    let R := 3*((d + 1)*(2*P + 4) + d + 1) + 16
    let r := spatialSiteRadius G K (vectorSpatialAccuracy d (2 + G*C) ε)
    (intervalSiteCount 1 r : ℝ) ≤ Real.exp (2*R + 4) ∧
      d * ((2*(intervalSiteCount 1 r : ℝ) + 1) / r) ≤ Real.exp (3*R + 6 + d) ∧
      (m^n * (intervalSiteCount 1 r : ℝ)^n * (G*C))^d ≤
        Real.exp (d * ((3*R + 4)*n + 2*R)) := by
  dsimp only
  let R := 3*((d + 1 : ℝ)*(2*P + 4) + d + 1) + 16
  let r := spatialSiteRadius G K (vectorSpatialAccuracy d (2 + G*C) ε)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hPR : P ≤ R := by dsimp [R]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hr : 0 < r := spatialSiteRadius_pos hG0 hK0
    (vectorSpatialAccuracy_pos d (by positivity) hε)
  have hri : 1 / r ≤ Real.exp R := vectorSpatial_radius_inverse_budget d hG0 hC0 hK0 hε hP hG hC hK hεi
  have hone : 1 ≤ Real.exp R := Real.one_le_exp_iff.mpr hR
  have hM := intervalSiteCount_le_exp zero_le_one hr hR hone hri
  have hLip := intervalSiteLipschitz_le_exp zero_le_one hr hR hone hri
  refine ⟨hM, vectorSiteLipschitz_le_exp d (by positivity) hLip, ?_⟩
  apply vectorSiteAllowance_le_exp d (by positivity)
  exact siteCoefficientAllowance_le_exp n hm0 (Nat.cast_nonneg _) hG0 hC0
    (hm.trans (Real.exp_le_exp.mpr hPR)) hM
    (hG.trans (Real.exp_le_exp.mpr hPR)) (hC.trans (Real.exp_le_exp.mpr hPR))

end Erdos3

end

end OAI

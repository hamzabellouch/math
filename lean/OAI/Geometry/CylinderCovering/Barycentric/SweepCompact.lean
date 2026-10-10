import OAI.Geometry.CylinderCovering.Barycentric.SweepsDefinitions
import OAI.Geometry.CylinderCovering.Radial.Coordinates

namespace OAI

namespace RadialCoordinates
open Set

private theorem barycentric_cap_pos (k t : ℝ) : 0 < cap k t := by
  unfold cap capPolynomial
  positivity

private theorem firstSweepPoint_first (k t S p : ℝ) :
    firstSweepPoint k t S p 0 = S * t + k * p * t ^ 2 := by
  simp [firstSweepPoint, barycentricPoint, angular]
  ring

private theorem firstSweepPoint_second (k t S p : ℝ) :
    firstSweepPoint k t S p 1 = S * (1 - t) - k * p * (1 - t) ^ 2 := by
  simp [firstSweepPoint, barycentricPoint, angular]
  ring

private theorem firstSweepPoint_difference (k t S p : ℝ) :
    firstSweepPoint k t S p 2 - firstSweepPoint k t S p 3 = p := by
  simp [firstSweepPoint, barycentricPoint]
  ring

private theorem firstSweepPoint_eq {v : BarycentricSpace} {k t S : ℝ}
    (hsum : ∑ i, v i = 1)
    (ha : v 0 = S * t + k * (v 2 - v 3) * t ^ 2)
    (hb : v 1 = S * (1 - t) - k * (v 2 - v 3) * (1 - t) ^ 2) :
    firstSweepPoint k t S (v 2 - v 3) = v := by
  have heq := radial_representation_sum_difference ha hb
  unfold firstSweepPoint
  rw [← heq.1, ← heq.2]
  exact barycentricPoint_reconstruct hsum

theorem firstSweep_eq_image (k : ℝ) :
    firstSweep k = (fun x : ℝ × ℝ × ℝ =>
      firstSweepPoint k x.1 (x.2.1 * cap k x.1) x.2.2) ''
        (Icc 0 1 ×ˢ (Icc 0 1 ×ˢ Icc (-1) 1)) := by
  ext v
  constructor
  · rintro ⟨hsum, t, S, ht, hS, hcap, hp, ha, hb⟩
    have hc := barycentric_cap_pos k t
    refine ⟨(t, S / cap k t, v 2 - v 3), ?_, ?_⟩
    · exact ⟨ht, ⟨div_nonneg hS (le_of_lt hc), (div_le_one hc).2 hcap⟩,
        abs_le.mp hp⟩
    · simp only [div_mul_cancel₀ S (ne_of_gt hc)]
      exact firstSweepPoint_eq hsum ha hb
  · rintro ⟨⟨t, u, p⟩, ⟨ht, hu, hp⟩, rfl⟩
    have hc := barycentric_cap_pos k t
    refine ⟨barycentricPoint_sum _ _ _, t, u * cap k t, ht,
      mul_nonneg hu.1 (le_of_lt hc), ?_, ?_, ?_, ?_⟩
    · exact mul_le_of_le_one_left (le_of_lt hc) hu.2
    · rw [firstSweepPoint_difference]
      exact abs_le.mpr hp
    · rw [firstSweepPoint_difference, firstSweepPoint_first]
    · rw [firstSweepPoint_difference, firstSweepPoint_second]

theorem firstSweep_isCompact (k : ℝ) : IsCompact (firstSweep k) := by
  rw [firstSweep_eq_image]
  apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image
  unfold firstSweepPoint barycentricPoint cap capPolynomial angular
  fun_prop

private theorem secondSweepPoint_first (k r T q : ℝ) :
    secondSweepPoint k r T q 2 = T * r - k * q * r ^ 2 := by
  simp [secondSweepPoint, barycentricPoint, angular]
  ring

private theorem secondSweepPoint_second (k r T q : ℝ) :
    secondSweepPoint k r T q 3 = T * (1 - r) + k * q * (1 - r) ^ 2 := by
  simp [secondSweepPoint, barycentricPoint, angular]
  ring

private theorem secondSweepPoint_difference (k r T q : ℝ) :
    secondSweepPoint k r T q 0 - secondSweepPoint k r T q 1 = q := by
  simp [secondSweepPoint, barycentricPoint]
  ring

private theorem secondSweepPoint_eq {v : BarycentricSpace} {k r T : ℝ}
    (hsum : ∑ i, v i = 1)
    (hc : v 2 = T * r - k * (v 0 - v 1) * r ^ 2)
    (hd : v 3 = T * (1 - r) + k * (v 0 - v 1) * (1 - r) ^ 2) :
    secondSweepPoint k r T (v 0 - v 1) = v := by
  have hsum' : v 0 + v 1 + v 2 + v 3 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  have hcd : v 2 + v 3 = T - k * (v 0 - v 1) * angular r := by
    unfold angular
    nlinarith only [hc, hd]
  have hdiff : v 2 - v 3 = T * angular r - k * (v 0 - v 1) *
      (1 + angular r ^ 2) / 2 := by
    unfold angular
    nlinarith only [hc, hd]
  have hab : v 0 + v 1 = 1 - T + k * (v 0 - v 1) * angular r := by
    linarith only [hsum', hcd]
  unfold secondSweepPoint
  rw [← hab, ← hdiff]
  exact barycentricPoint_reconstruct hsum

theorem secondSweep_eq_image (k : ℝ) :
    secondSweep k = (fun x : ℝ × ℝ × ℝ =>
      secondSweepPoint k x.1 (x.2.1 * cap k x.1) x.2.2) ''
        (Icc 0 1 ×ˢ (Icc 0 1 ×ˢ Icc (-1) 1)) := by
  ext v
  constructor
  · rintro ⟨hsum, r, T, hr, hT, hcap, hq, hc, hd⟩
    have hcap0 := barycentric_cap_pos k r
    refine ⟨(r, T / cap k r, v 0 - v 1), ?_, ?_⟩
    · exact ⟨hr, ⟨div_nonneg hT (le_of_lt hcap0), (div_le_one hcap0).2 hcap⟩,
        abs_le.mp hq⟩
    · simp only [div_mul_cancel₀ T (ne_of_gt hcap0)]
      exact secondSweepPoint_eq hsum hc hd
  · rintro ⟨⟨r, u, q⟩, ⟨hr, hu, hq⟩, rfl⟩
    have hcap0 := barycentric_cap_pos k r
    refine ⟨barycentricPoint_sum _ _ _, r, u * cap k r, hr,
      mul_nonneg hu.1 (le_of_lt hcap0), ?_, ?_, ?_, ?_⟩
    · exact mul_le_of_le_one_left (le_of_lt hcap0) hu.2
    · rw [secondSweepPoint_difference]
      exact abs_le.mpr hq
    · rw [secondSweepPoint_difference, secondSweepPoint_first]
    · rw [secondSweepPoint_difference, secondSweepPoint_second]

theorem secondSweep_isCompact (k : ℝ) : IsCompact (secondSweep k) := by
  rw [secondSweep_eq_image]
  apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).image
  unfold secondSweepPoint barycentricPoint cap capPolynomial angular
  fun_prop

theorem firstSweep_isClosed (k : ℝ) : IsClosed (firstSweep k) :=
  (firstSweep_isCompact k).isClosed

theorem secondSweep_isClosed (k : ℝ) : IsClosed (secondSweep k) :=
  (secondSweep_isCompact k).isClosed

theorem firstSweep_eq_withCap (k : ℝ) : firstSweep k = firstSweepWithCap k (cap k) := by
  ext v
  constructor
  · rintro ⟨hsum, t, S, ht, hS, hcap, hp, ha, hb⟩
    exact ⟨((t, S), v 2 - v 3), ⟨⟨ht, hS, hcap⟩, abs_le.mp hp⟩,
      firstSweepPoint_eq hsum ha hb⟩
  · rintro ⟨⟨⟨t, S⟩, p⟩, ⟨⟨ht, hS, hcap⟩, hp⟩, rfl⟩
    refine ⟨barycentricPoint_sum _ _ _, t, S, ht, hS, hcap, ?_, ?_, ?_⟩
    · rw [firstSweepPoint_difference]; exact abs_le.mpr hp
    · rw [firstSweepPoint_difference, firstSweepPoint_first]
    · rw [firstSweepPoint_difference, firstSweepPoint_second]

theorem secondSweep_eq_withCap (k : ℝ) : secondSweep k = secondSweepWithCap k (cap k) := by
  ext v
  constructor
  · rintro ⟨hsum, r, T, hr, hT, hcap, hq, hc, hd⟩
    exact ⟨((r, T), v 0 - v 1), ⟨⟨hr, hT, hcap⟩, abs_le.mp hq⟩,
      secondSweepPoint_eq hsum hc hd⟩
  · rintro ⟨⟨⟨r, T⟩, q⟩, ⟨⟨hr, hT, hcap⟩, hq⟩, rfl⟩
    refine ⟨barycentricPoint_sum _ _ _, r, T, hr, hT, hcap, ?_, ?_, ?_⟩
    · rw [secondSweepPoint_difference]; exact abs_le.mpr hq
    · rw [secondSweepPoint_difference, secondSweepPoint_first]
    · rw [secondSweepPoint_difference, secondSweepPoint_second]

end RadialCoordinates

end OAI

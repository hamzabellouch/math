import OAI.Geometry.CylinderCovering.Nilpotent.Counterexample

namespace OAI

noncomputable section
open Set MeasureTheory RuledApproximation

namespace CylinderCovering.Nilpotent

lemma exists_source_collar {k ε : ℝ} (hk : 0 ≤ k) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 2 ∧ 32 * (1 + k / 2) ^ 2 * ρ < ε := by
  have hden : 0 < 32 * (1 + k / 2) ^ 2 := by positivity
  obtain ⟨ρ, hρ, hρupper⟩ := exists_between
    (lt_min (by norm_num : (0 : ℝ) < 1 / 2) (div_pos hε hden))
  refine ⟨ρ, hρ, (lt_min_iff.mp hρupper).1, ?_⟩
  simpa only [mul_comm] using
    (lt_div_iff₀ hden).mp (lt_min_iff.mp hρupper).2

theorem signed_sweep_finite_at_tolerance {k σ ε : ℝ} (hk : 0 ≤ k)
    (hσ : |σ| ≤ 1) (hsq : (σ * k) ^ 2 = k ^ 2) (hε : 0 < ε) :
    HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap (Real.sqrt 2) '' signedSweep (σ * k) k)
      (Real.sqrt 2 * (I k + ε)) := by
  obtain ⟨ρ, hρ, hρhalf, hbudget⟩ := exists_source_collar hk hε
  exact complete_signed_cover hk hσ hsq hρ hρhalf.le hε hbudget.le

theorem tetrahedron_finite_at_tolerance {k ε : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hε : 0 < ε) :
    HasFiniteCover Cylinder.parallelogram tetrahedron
      (2 * Real.sqrt 2 * (I k + ε)) := by
  have hpos : HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap (Real.sqrt 2) '' signedSweep k k)
      (Real.sqrt 2 * (I k + ε)) := by
    simpa using signed_sweep_finite_at_tolerance (σ := 1) hk.le
      (by norm_num) (by ring) hε
  have hneg : HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap (Real.sqrt 2) '' signedSweep (-k) k)
      (Real.sqrt 2 * (I k + ε)) := by
    simpa using signed_sweep_finite_at_tolerance (σ := -1) hk.le
      (by norm_num) (by ring) hε
  exact (hpos.union (physical_second_cover (a := 1) hneg)).mono
    (tetrahedron_subset_signed_sweeps hk hk1) (by ring_nf; rfl)

theorem finite_counterexample_of_integral_saving {k : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hsaving : I k < 1 / 4) :
    ∃ n : ℕ, ∃ C : Fin n → Cylinder,
      (∀ i, (C i).parallelogram ∧ IsCompact (C i).base ∧ Convex ℝ (C i).base) ∧
      tetrahedron ⊆ familySet C ∧
      familyArea C < minimumShadowArea tetrahedron / 2 ∧
      relativeCost tetrahedron C < 1 / 2 := by
  obtain ⟨ε, hε, hεsmall⟩ := exists_between (sub_pos.mpr hsaving)
  obtain ⟨n, C, hC, hcover, hcost⟩ := tetrahedron_finite_at_tolerance hk hk1 hε
  have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hstrict : familyArea C < Real.sqrt 2 / 2 := by
    have hslack : I k + ε < 1 / 4 := by linarith
    have hmul := mul_lt_mul_of_pos_left hslack (show 0 < 2 * Real.sqrt 2 by positivity)
    nlinarith
  refine ⟨n, C, fun i => ⟨hC i, (hC i).isCompact, (hC i).convex⟩,
    hcover, ?_, ?_⟩
  · rwa [ruled_tetrahedron_minimum_shadow]
  · apply lt_of_le_of_lt (relativeCost_le_normalized_area C)
    apply (div_lt_iff₀ hroot).2
    linarith

end CylinderCovering.Nilpotent

end

end OAI

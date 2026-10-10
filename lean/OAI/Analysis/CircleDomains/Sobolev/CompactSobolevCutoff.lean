import OAI.Analysis.CircleDomains.Sobolev.PositiveSobolevApproximation

namespace OAI

/-! Smooth compact cutoffs turn local planar Sobolev functions into
global Sobolev functions, to which positive mollification applies. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem memW1p_mul_compact_cutoff
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω) {u η : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1p 2 u Ω) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) : DeGiorgi.MemW1p 2 (fun x => η x * u x) Ω := by
  obtain ⟨A, hA⟩ := hη.continuous.bounded_above_of_compact_support hsη
  obtain ⟨B, hB⟩ := (hη.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hsη.fderiv (𝕜 := ℝ))
  exact (hu.someWitness.mul_smooth_bounded_p (by norm_num) hΩ hη
    (le_max_right A 0) (le_max_right B 0)
    (fun x => by simpa only [Real.norm_eq_abs] using (hA x).trans (le_max_left A 0))
    (fun x => (hB x).trans (le_max_left B 0))).memW1p

theorem exists_global_compact_cutoff_witness
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω) {u η : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1p 2 u Ω) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) (hsub : tsupport η ⊆ Ω) :
    Nonempty (DeGiorgi.MemW1pWitness 2 (fun x => η x * u x) univ) := by
  let v : EuclideanPlane → ℝ := fun x => η x * u x
  have hv : DeGiorgi.MemW1p 2 v Ω := memW1p_mul_compact_cutoff hΩ hu hη hsη
  have hsv : HasCompactSupport v := hsη.mul_right
  have hsubv : tsupport v ⊆ Ω := (tsupport_mul_subset_left).trans hsub
  have hv' : DeGiorgi.MemW1p (ENNReal.ofReal (2 : ℝ)) v Ω := by simpa using hv
  have hzero := DeGiorgi.memW01p_of_memW1p_of_tsupport_subset
    (p := 2) hΩ (by norm_num) hv' hsv hsubv
  have hi : Ω.indicator v = v := by
    funext x
    by_cases hx : x ∈ Ω
    · exact indicator_of_mem hx v
    · rw [indicator_of_notMem hx]
      exact (DeGiorgi.zero_outside_of_tsupport_subset hsubv hx).symm
  have hw := DeGiorgi.zeroExtend_memW1pWitness_p (p := 2) hΩ (by norm_num) hzero hv'.someWitness
  rw [hi] at hw
  exact ⟨by simpa using hw⟩

theorem compact_cutoff_mem_Icc
    {Ω : Set EuclideanPlane} {u η : EuclideanPlane → ℝ}
    (hu : ∀x ∈ Ω, u x ∈ Icc 0 1) (hη : ∀x, η x ∈ Icc 0 1)
    (hsub : tsupport η ⊆ Ω) (x : EuclideanPlane) : η x * u x ∈ Icc 0 1 := by
  by_cases hx : x ∈ Ω
  · exact ⟨mul_nonneg (hη x).1 (hu x hx).1,
      (mul_le_mul (hη x).2 (hu x hx).2 (hu x hx).1 zero_le_one).trans_eq (one_mul 1)⟩
  · have hzero : η x = 0 := by
      by_contra hn
      exact hx (hsub (subset_tsupport η hn))
    simp only [hzero, zero_mul, mem_Icc, le_rfl, zero_le_one, and_self]

end CircleDomainRigidity

end

end OAI

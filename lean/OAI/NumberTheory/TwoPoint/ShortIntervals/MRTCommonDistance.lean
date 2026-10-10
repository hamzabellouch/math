import OAI.NumberTheory.TwoPoint.Halasz.HalaszDistanceCutoff

namespace OAI

/-! A single original-cutoff distance condition supplies both dyadic
kernel endpoints. The loss is absolute and is truncated at zero. -/

namespace TwoPointCorrelations

open Finset

/-- The same distance lower bound, with one fixed loss, holds at all
endpoints `2*k` for `N≤k≤2*N`, hence in particular at `2*N` and `4*N`. -/
theorem mrt_common_distance_lower_bound : ∃ K : ℝ, 0≤K ∧
    ∀ N : ℕ, 1≤N → ∀ F : ℕ → ℂ, OneBounded F → ∀ M : ℝ,
      (∀ v : ℝ, |v|≤4*N → M≤squaredDistance F (mrtArchimedeanTwist v) (4*N)) →
      ∀ k∈Icc N (2*N), ∀ v : ℝ, |v|≤2*k →
        max 0 (M-K)≤squaredDistance F (mrtArchimedeanTwist v) (2*k) := by
  obtain ⟨K,hK,hcut⟩ := halasz_distance_cutoff_loss
  refine ⟨K,hK,?_⟩
  intro N hN F hF M hM k hk v hv
  obtain ⟨hNk,hkN⟩ := mem_Icc.mp hk
  have hk1 : 1≤k := hN.trans hNk
  have htwo : 2≤2*k := by omega
  have horder : 2*k≤4*N := by omega
  have hcube : 4*N≤(2*k)^3 := by
    have hs : 2≤(2*k)^2 := by nlinarith
    calc
      4*N ≤ 2*(2*k) := by omega
      _ ≤ (2*k)^2*(2*k) := Nat.mul_le_mul_right (2*k) hs
      _ = (2*k)^3 := by ring
  have hv' : |v|≤4*N := hv.trans (by exact_mod_cast horder)
  have hloss := hcut F hF (2*k) (4*N) htwo horder hcube v
  apply max_le (halasz_distance_nonneg F hF (2*k) v)
  linarith [hM v hv']

/-- The two actual endpoints used by the logarithmic kernel have one
uniform original-cutoff lower bound. -/
theorem mrt_two_endpoint_distance : ∃ K : ℝ, 0≤K ∧
    ∀ N : ℕ, 1≤N → ∀ F : ℕ → ℂ, OneBounded F → ∀ M : ℝ,
      (∀ v : ℝ, |v|≤4*N → M≤squaredDistance F (mrtArchimedeanTwist v) (4*N)) →
      ∀ k∈({N,2*N}:Finset ℕ), ∀ v : ℝ, |v|≤2*k →
        max 0 (M-K)≤squaredDistance F (mrtArchimedeanTwist v) (2*k) := by
  obtain ⟨K,hK,hlower⟩ := mrt_common_distance_lower_bound
  refine ⟨K,hK,?_⟩
  intro N hN F hF M hM k hk v hv
  have hk' : k∈Icc N (2*N) := by
    simp only [mem_insert,mem_singleton] at hk
    rcases hk with rfl | rfl <;> apply mem_Icc.mpr <;> constructor <;> omega
  exact hlower N hN F hF M hM k hk' v hv

end TwoPointCorrelations

end OAI

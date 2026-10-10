import Mathlib.Tactic

namespace OAI

/-! # Choosing the simultaneous smallness parameters for sharp projection -/

namespace RegularPointCoordinates

/-- One positive choice satisfies the coordinate, source, and curvature
requirements, while making the two-center square budget arbitrarily small. -/
theorem sharp_neighborhood_parameters {epsilon delta tau c g a K budget : ℝ}
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (htau : 0 < tau)
    (hc : 0 ≤ c) (hg : 0 ≤ g) (ha : 0 ≤ a) (hbudget : 0 < budget) :
    ∃ zeta eta cap : ℝ, 0 < zeta ∧ 0 < eta ∧ 0 < cap ∧
      zeta ≤ epsilon ∧ zeta ≤ delta ∧ c * zeta ≤ 1 ∧ g * zeta ≤ 1 / 64 ∧
      eta ≤ tau ∧ 128 * (a * zeta + eta) ≤ budget ∧ |K| * cap ^ 2 ≤ delta / 32 := by
  let zeta := min epsilon (min delta (min (1 / (c + 1))
    (min (1 / (64 * (g + 1))) (budget / (512 * (a + 1))))))
  let eta := min tau (budget / 512)
  let cap := min 1 (delta / (32 * (|K| + 1)))
  have hzeta : 0 < zeta := by
    dsimp only [zeta]
    positivity
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hcap : 0 < cap := by dsimp only [cap]; positivity
  have hzbound : zeta ≤ min epsilon (min delta (min (1 / (c + 1))
      (min (1 / (64 * (g + 1))) (budget / (512 * (a + 1)))))) := le_rfl
  simp only [le_min_iff] at hzbound
  obtain ⟨hze, hzd, hzc, hzg, hza⟩ := hzbound
  have hzc' := (le_div_iff₀ (by positivity : 0 < c + 1)).mp hzc
  have hzg' := (le_div_iff₀ (by positivity : 0 < 64 * (g + 1))).mp hzg
  have hza' := (le_div_iff₀ (by positivity : 0 < 512 * (a + 1))).mp hza
  have hetatau : eta ≤ tau := min_le_left _ _
  have hetab : eta ≤ budget / 512 := min_le_right _ _
  have hcap1 : cap ≤ 1 := min_le_left _ _
  have hcapd : cap ≤ delta / (32 * (|K| + 1)) := min_le_right _ _
  have hcapd' := (le_div_iff₀ (by positivity : 0 < 32 * (|K| + 1))).mp hcapd
  have hsquare : cap ^ 2 ≤ cap := by nlinarith
  have hcurv := mul_le_mul_of_nonneg_left hsquare (abs_nonneg K)
  refine ⟨zeta, eta, cap, hzeta, heta, hcap, hze, hzd, ?_, ?_, hetatau, ?_, ?_⟩ <;> nlinarith

end RegularPointCoordinates

end OAI

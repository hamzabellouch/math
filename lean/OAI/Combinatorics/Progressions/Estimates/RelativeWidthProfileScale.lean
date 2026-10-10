import OAI.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget

namespace OAI

section

namespace Erdos3

theorem residueProfileWidth_large_of_exp_size {K X : Type*} {P ρ : ℝ}
    (hP : 0 ≤ P) (hρ : 0 < ρ) (hρP : 1 / ρ ≤ Real.exp P)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (hmodP : ∀ i, (modulus i : ℝ) ≤ Real.exp P)
    (H : X → ℝ) (hH : ∀ i, Real.exp (5*P+128) ≤ H i)
    (W : K × X → ℝ) (hwidth : ∀ z, ρ * H z.2 ≤ W z) (z : K × X) :
    8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z := by
  have hm : (0 : ℝ) < modulus z.2 := by exact_mod_cast hmodulus z.2
  apply (le_div_iff₀ hm).mpr
  have hsize := spatial_scale_of_exp_size hP hρ (by simpa only [one_div] using hρP)
    (Nat.cast_nonneg (modulus z.2)) (hmodP z.2) hprofile (hH z.2)
  have hp : 0 ≤ (probabilityProfileLipschitz : ℝ) * (modulus z.2 : ℝ) := by positivity
  have hs : 8*(probabilityProfileLipschitz : ℝ)*(modulus z.2 : ℝ) ≤
      64*(probabilityProfileLipschitz : ℝ)*(modulus z.2 : ℝ)*(1+Real.exp (2*P)) := by
    nlinarith [Real.exp_pos (2*P)]
  exact hs.trans (hsize.trans (hwidth z))

end Erdos3

end

end OAI

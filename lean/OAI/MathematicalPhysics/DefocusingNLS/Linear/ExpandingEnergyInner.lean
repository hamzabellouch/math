import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEnergyScaling
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace OAI

/-! # Polarization of the exact expanding-torus energy identities -/

namespace DefocusingNLS

theorem expandingEnergy_inner (a k L : ℝ) (hL : 1 ≤ L) (f g : FourierL2) :
    inner ℝ f g = inner ℝ (expandingLowEnergy a k L hL f) (expandingLowEnergy a k L hL g) +
      inner ℝ (expandingHighEnergy a k L hL f) (expandingHighEnergy a k L hL g) := by
  have h := expandingEnergy_norm_sq a k L hL (f + g)
  simp only [map_add] at h
  rw [norm_add_sq_real, norm_add_sq_real, norm_add_sq_real,
    expandingEnergy_norm_sq a k L hL f, expandingEnergy_norm_sq a k L hL g] at h
  linarith

theorem expandingLowEnergy_free_inner (a b k L s : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) (f g : FourierL2) :
    inner ℝ (expandingLowEnergy a k (expandingRadius L s)
        (hL.trans (expandingRadius_ge L s hL hs)) (expandingFreeStep a b k L s ha hk hL hs f))
      (expandingLowEnergy a k (expandingRadius L s)
        (hL.trans (expandingRadius_ge L s hL hs)) (expandingFreeStep a b k L s ha hk hL hs g)) =
      Real.exp (-a * s) * inner ℝ (expandingLowEnergy a k L hL f) (expandingLowEnergy a k L hL g) := by
  have h := expandingLowEnergy_free a b k L s ha hk hL hs (f + g)
  simp only [map_add] at h
  rw [norm_add_sq_real, norm_add_sq_real,
    expandingLowEnergy_free a b k L s ha hk hL hs f,
    expandingLowEnergy_free a b k L s ha hk hL hs g] at h
  nlinarith [h]

theorem expandingHighEnergy_free_inner (a b k L s : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hs : 0 ≤ s) (f g : FourierL2) :
    inner ℝ (expandingHighEnergy a k (expandingRadius L s)
        (hL.trans (expandingRadius_ge L s hL hs)) (expandingFreeStep a b k L s ha hk hL hs f))
      (expandingHighEnergy a k (expandingRadius L s)
        (hL.trans (expandingRadius_ge L s hL hs)) (expandingFreeStep a b k L s ha hk hL hs g)) =
      Real.exp ((6 - 2 * a - k) * s) *
        inner ℝ (expandingHighEnergy a k L hL f) (expandingHighEnergy a k L hL g) := by
  have h := expandingHighEnergy_free a b k L s ha hk hL hs (f + g)
  simp only [map_add] at h
  rw [norm_add_sq_real, norm_add_sq_real,
    expandingHighEnergy_free a b k L s ha hk hL hs f,
    expandingHighEnergy_free a b k L s ha hk hL hs g] at h
  nlinarith [h]

end DefocusingNLS

end OAI

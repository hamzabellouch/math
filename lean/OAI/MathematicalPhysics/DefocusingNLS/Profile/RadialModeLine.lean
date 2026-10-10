import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCanonicalModeLine
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeValueRadius
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPenaltyFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchingParameterLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingCanonicalSelection

namespace OAI

/-! # Actual radial mode lines along converging matched profiles -/

open Filter Topology Set

namespace DefocusingNLS
open ProfileCertificate

def RadialModeLine (n : ℕ) (z : ProfileMatchingBall) (ell N : ℕ) (lam : ℂ) : Prop :=
  ∀ u v : RadialSpectralMode (radialShootingA n)
    (radialShootingB (profileMatchingParameter z)) (n + radialInnerShootingThreshold) N
    (radialMatchedProfile n z) ((ell : ℂ) * (ell + 10)) lam,
    ∃ c : ℂ, ∀ r : ℝ, 0 < r → v.first r = c * u.first r ∧ v.second r = c * u.second r

theorem radialMatched_mode_line_along (hRou : RectangleRouche) (ell N : ℕ) (hN : 7 ≤ N)
    (lam : ℂ) (hsym : (ell = 0 ∧ (lam = 0 ∨ lam = 1)) ∨ (ell = 1 ∧ lam = 1 / 2))
    (s : ℕ → ℕ) (hs : StrictMono s) (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i + radialInnerShootingThreshold) (z i))
      (s i + radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i) = 0) :
    ∃ i, RadialModeLine (s i) (z i) ell N lam := by
  obtain ⟨hz₁, hz₀⟩ := radialMatchingMap_zero_limit s hs.tendsto_atTop z z₀ hz hm
  have hhalf : -(1 / 32 : ℝ) ≤ lam.re := by
    rcases hsym with ⟨_, rfl | rfl⟩ | ⟨_, rfl⟩ <;> norm_num
  obtain ⟨R, hR, hLR, hdet⟩ := radialFreeValueDet_large_radius ell z₀ lam hhalf
  obtain ⟨K, F, hw, hmass, hp, ha, _⟩ := radialMatched_penaltyFamily s hs z z₀ hz hX hm R hR.le
  let t := fun i => s (i + K)
  let y := fun i => z (i + K)
  have ht : StrictMono t := fun i j hij => hs (Nat.add_lt_add_right hij K)
  have hshift : Tendsto (fun i : ℕ => i + K) atTop atTop := tendsto_add_atTop_nat K
  have hy : Tendsto y atTop (𝓝 z₀) := hz.comp hshift
  have hXt (i : ℕ) : HasRadialExterior (radialShootingNu (t i + radialInnerShootingThreshold) (y i))
      (t i + radialInnerShootingThreshold) (radialShootingM (y i)) (Real.log innerBoundaryRadius) :=
    hX (i + K)
  have hmt (i : ℕ) : radialMatchingMap (t i) (y i) = 0 := hm (i + K)
  obtain ⟨Y, hY⟩ := radialMatched_exists_canonical_column t y hXt ell (1, 0)
  obtain ⟨Z, hZ⟩ := radialMatched_exists_canonical_column t y hXt ell (0, 1)
  have hline := radialMatchedCanonical_modes_proportional hRou t ht y z₀ hy hz₁ hz₀ hXt hmt
    ell N hN Y Z hY hZ R hR hLR F hmass hw hp ha lam hsym hdet (fun _ => lam) tendsto_const_nhds
  obtain ⟨i, hi⟩ := hline.exists
  exact ⟨i + K, hi⟩

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialModeNoSplitting
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeValueRadius
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPenaltyFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchingParameterLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingCanonicalSelection

namespace OAI

/-! Extra actual eigenvalues cannot approach any of the three symmetry values. -/

open Filter Topology
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatchedMode_no_extra_limit (hRou : RectangleRouche) (ell N : ℕ) (hN : 7 ≤ N)
    (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (x : ℕ → ℂ) (lam₀ : ℂ) (hx : Tendsto x atTop (𝓝 lam₀))
    (hsym : (ell=0 ∧ (lam₀=0 ∨ lam₀=1)) ∨ (ell=1 ∧ lam₀=1/2))
    (hne : ∀ᶠ i in atTop, x i ≠ lam₀)
    (hhalf : ∀ i, -(1/32 : ℝ) ≤ (x i).re)
    (mode : ∀ i, RadialSpectralMode (radialShootingA (s i))
      (radialShootingB (profileMatchingParameter (z i))) (s i+radialInnerShootingThreshold) N
      (radialMatchedProfile (s i) (z i)) ((ell : ℂ)*(ell+10)) (x i)) : False := by
  obtain ⟨hz₁,hz₀⟩ := radialMatchingMap_zero_limit s hs.tendsto_atTop z z₀ hz hm
  have hhalf₀ : -(1/32 : ℝ) ≤ lam₀.re := by
    rcases hsym with ⟨_,rfl | rfl⟩ | ⟨_,rfl⟩ <;> norm_num
  obtain ⟨R,hR,hLR,hdet⟩ := radialFreeValueDet_large_radius ell z₀ lam₀ hhalf₀
  obtain ⟨K,F,hw,hmass,hp,ha,_⟩ := radialMatched_penaltyFamily s hs z z₀ hz hX hm R hR.le
  let t := fun i => s (i+K)
  let y := fun i => z (i+K)
  have ht : StrictMono t := fun i j hij => hs (Nat.add_lt_add_right hij K)
  have hshift : Tendsto (fun i : ℕ => i+K) atTop atTop := tendsto_add_atTop_nat K
  have hy : Tendsto y atTop (𝓝 z₀) := hz.comp hshift
  have hXt (i : ℕ) : HasRadialExterior (radialShootingNu (t i+radialInnerShootingThreshold) (y i))
      (t i+radialInnerShootingThreshold) (radialShootingM (y i)) (Real.log innerBoundaryRadius) := hX (i+K)
  have hmt (i : ℕ) : radialMatchingMap (t i) (y i)=0 := hm (i+K)
  obtain ⟨Y,hY⟩ := radialMatched_exists_canonical_column t y hXt ell (1,0)
  obtain ⟨Z,hZ⟩ := radialMatched_exists_canonical_column t y hXt ell (0,1)
  exact radialMatchedMode_no_extra_sequence hRou t ht y z₀ hy hz₁ hz₀ hXt hmt ell
    Y Z hY hZ R hR hLR F hmass lam₀ hsym hdet hw hp ha N hN
    (fun i => x (i+K)) (hx.comp hshift) (hshift.eventually hne)
    (fun i => hhalf (i+K)) (fun i => mode (i+K))

end DefocusingNLS

end OAI

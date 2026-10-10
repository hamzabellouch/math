import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalPath
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingStrongEquation

namespace OAI

/-! # The moving-scale mild solution is a strong Sobolev solution

Pulling back the exact weights identifies the changing spaces with the
radius-one Fourier space. The resulting curve satisfies the physical
Schrödinger equation with the expected two-derivative loss.
-/

open Set

namespace DefocusingNLS

theorem hasDerivAt_expandingMild_strong (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (r : ℝ → FourierL2) (hr : Continuous r)
    (u₀ : FourierL2)
    (hu : ∀ s : Icc (0 : ℝ) T, u s =
      expandingFreeStep a b k L s ha hk hL s.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL s r)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    let rC : C(Icc (0 : ℝ) T, FourierL2) := ⟨fun s => r s, hr.comp continuous_subtype_val⟩
    let w := fun s => expandingPhysicalPath a k L T ha hk hL u (projIcc 0 T hT s)
    let j := fun s => expandingPhysicalPath a k L T ha hk hL rC (projIcc 0 T hT s)
    HasDerivAt (fun s => lowerSobolevInclusion (w s)) (expandingReducedField a b L w j t) t := by
  intro rC w j
  apply hasDerivAt_expandingReducedField a b L 0 T w j
    (((expandingPhysicalPath a k L T ha hk hL u).continuous.comp continuous_projIcc).continuousOn)
    (((expandingPhysicalPath a k L T ha hk hL rC).continuous.comp continuous_projIcc).continuousOn)
    _ t ht
  intro s hs n
  let uExt := fun τ => u (projIcc 0 T hT τ)
  have hue (τ : ℝ) (hτ : τ ∈ Icc 0 T) : uExt τ =
      expandingFreeStep a b k L τ ha hk hL hτ.1 u₀ +
        expandingDuhamel a b k L ha hk hL τ r := by
    change u (projIcc 0 T hT τ) = _
    rw [projIcc_of_mem _ hτ]
    exact hu ⟨τ, hτ⟩
  have hm := hasDerivAt_expandingMild_coefficient a b k L T ha hk hL uExt r u₀
    hr.continuousOn hue s hs n
  have hp := hasDerivAt_expandingPhysicalPath_coordinate a k L T ha hk hL hT u s hs n
    _ hm
  apply hp.congr_deriv
  change (expandingSobolevWeight a k 1 n : ℂ) *
      (expandingModeRate a b L s n *
          expandingFourierCoefficient a k (expandingRadius L s) (uExt s) n +
        expandingFourierCoefficient a k (expandingRadius L s) (r s) n) =
    expandingModeRate a b L s n *
      expandingPhysicalPath a k L T ha hk hL u (projIcc 0 T hT s) n +
      expandingPhysicalPath a k L T ha hk hL rC (projIcc 0 T hT s) n
  dsimp [uExt]
  rw [projIcc_of_mem _ ⟨hs.1.le, hs.2.le⟩,
    expandingPhysicalPath_coefficient, expandingPhysicalPath_coefficient]
  change (expandingSobolevWeight a k 1 n : ℂ) * (_ * _ + _) =
    _ * ((expandingSobolevWeight a k 1 n : ℂ) * _) +
      (expandingSobolevWeight a k 1 n : ℂ) *
        expandingFourierCoefficient a k (expandingRadius L s) (r s) n
  ring

end DefocusingNLS

end OAI

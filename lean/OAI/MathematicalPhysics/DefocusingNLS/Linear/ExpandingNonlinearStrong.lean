import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingResidualStability
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMildStrong

namespace OAI

/-! # The actual nonlinear mild trajectory satisfies the strong equation

The coefficient-preserving inverse weight map intertwines the nonlinearities.
The resulting fixed-space curve has its strong derivative with two fewer
Sobolev derivatives, exactly as the linear and forced curves do.
-/

open Set

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep

theorem expandingInverseTransfer_oddPower (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ)
    (f : FourierL2) :
    expandingInverseTransfer a k L ha hk hL (expandingOddPower a k L ha ha1 hk hL m f) =
      expandingOddPower a k 1 ha ha1 hk le_rfl m
        (expandingInverseTransfer a k L ha hk hL f) := by
  rw [expandingOddPower_transport a k L ha ha1 hk hL m f]
  exact congrArg (fun A : FourierL2 →L[ℂ] FourierL2 =>
    A (expandingOddPower a k 1 ha ha1 hk le_rfl m
      (expandingInverseTransfer a k L ha hk hL f)))
    (expandingWeightUnit a k L ha hk hL).inv_val

theorem hasDerivAt_expandingNonlinearMild (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (u : C(Icc (0 : ℝ) T, FourierL2)) (u₀ : FourierL2)
    (hu : u = expandingPicard a b k L T ha hk hL hT
      (expandingNonlinearReaction a k L T ha ha1 hk hL m) u₀ u)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    let w := fun s => expandingPhysicalPath a k L T ha hk hL u (projIcc 0 T hT s)
    HasDerivAt (fun s => lowerSobolevInclusion (w s))
      ((-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (w t) +
        (L ^ (-2 : ℝ) * Real.exp (-t)) • lowerSobolevGenerator (w t) +
        (-Complex.I) • lowerSobolevInclusion
          (expandingOddPower a k 1 ha ha1 hk le_rfl m (w t))) t := by
  intro w
  let F := expandingNonlinearReaction a k L T ha ha1 hk hL m
  let r := expandingReactionHistory T hT F u
  have hr : Continuous r := continuous_expandingReactionHistory T hT F u
  have hu' (s : Icc (0 : ℝ) T) : u s =
      expandingFreeStep a b k L s ha hk hL s.2.1 u₀ +
        expandingDuhamel a b k L ha hk hL s r :=
    congrArg (fun v : C(Icc (0 : ℝ) T, FourierL2) => v s) hu
  have hs := hasDerivAt_expandingMild_strong a b k L T ha hk hL hT u r hr u₀ hu' t ht
  let rC : C(Icc (0 : ℝ) T, FourierL2) := ⟨fun s => r s, hr.comp continuous_subtype_val⟩
  let j := fun s => expandingPhysicalPath a k L T ha hk hL rC (projIcc 0 T hT s)
  change HasDerivAt (fun s => lowerSobolevInclusion (w s))
    (expandingReducedField a b L w j t) t at hs
  have hj : j t = (-Complex.I) • expandingOddPower a k 1 ha ha1 hk le_rfl m (w t) := by
    let s := projIcc 0 T hT t
    have hp : projIcc 0 T hT (s : ℝ) = s := projIcc_of_mem _ s.2
    have hR : 1 ≤ expandingRadius L s := hL.trans (expandingRadius_ge L s hL s.2.1)
    change expandingInverseTransfer a k (expandingRadius L s) ha hk
      hR (r s) = _
    change expandingInverseTransfer a k (expandingRadius L s) ha hk
      hR
      (F (projIcc 0 T hT s, u (projIcc 0 T hT s))) = _
    rw [hp]
    change expandingInverseTransfer a k (expandingRadius L s) ha hk
      hR
      ((-Complex.I) • expandingOddPower a k (expandingRadius L s) ha ha1 hk
        hR m (u s)) = _
    rw [map_smul, expandingInverseTransfer_oddPower a k (expandingRadius L s) ha ha1 hk hR m (u s)]
    rfl
  unfold expandingReducedField at hs
  rw [hj, map_smul] at hs
  exact hs

end DefocusingNLS

end OAI

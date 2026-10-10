import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRealPhysicalContour

namespace OAI

/-! # Physical coordinates on the real contour range -/

namespace DefocusingNLS

section
variable (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
local notation "H" => HomogeneousY a k
local notation "ι" => homogeneousComplexEmbed a k ha ha1 hk
local notation "X" => homogeneousComplexReal a k ha ha1 hk

theorem exists_physicalContour_coordinates
    (P : (H × H) →L[ℂ] (H × H))
    (F : ProfileSymmetryParameters →L[ℝ] H) (hF : Function.Injective F)
    (hfix : ∀ p, P (ι (F p)) = ι (F p))
    (hrange : ∀ u, ∃ p, P (ι u) = ι (F p)) :
    ∃ π : H →L[ℝ] ProfileSymmetryParameters,
      (∀ p, π (F p) = p) ∧
      (∀ u, ι (F (π u)) = P (ι u)) ∧
      (∀ u, π u = 0 ↔ homogeneousStableCoordinates a k ha ha1 hk P u = 0) := by
  let B := (X).comp ((P.restrictScalars ℝ).comp ι)
  have hB (u : H) : B u ∈ F.range := by
    obtain ⟨p, hp⟩ := hrange u
    refine ⟨p, ?_⟩
    change F p = X (P (ι u))
    rw [hp, homogeneousComplexReal_embed]
  let e : ProfileSymmetryParameters ≃L[ℝ] F.range :=
    (LinearEquiv.ofInjective F.toLinearMap hF).toContinuousLinearEquiv
  let π := e.symm.toContinuousLinearMap.comp (B.codRestrict F.range hB)
  have hπ (u : H) : F (π u) = B u := by
    exact congrArg (fun v : F.range => (v : H)) (e.apply_symm_apply ⟨B u, hB u⟩)
  have hπF (p : ProfileSymmetryParameters) : π (F p) = p := by
    apply hF
    rw [hπ]
    change X (P (ι (F p))) = F p
    rw [hfix, homogeneousComplexReal_embed]
  have hreal (u : H) : ι (F (π u)) = P (ι u) := by
    obtain ⟨p, hp⟩ := hrange u
    rw [hπ]
    change ι (X (P (ι u))) = P (ι u)
    rw [hp, homogeneousComplexReal_embed]
  refine ⟨π, hπF, hreal, fun u => ?_⟩
  rw [homogeneousStableCoordinates_zero_iff]
  constructor
  · intro h
    rw [← hreal, h, map_zero, map_zero]
  · intro h
    have he := hreal u
    rw [h] at he
    have hf0 : F (π u) = 0 := by
      have := congrArg X he
      simpa only [homogeneousComplexReal_embed, map_zero] using this
    exact hF (hf0.trans (map_zero F).symm)

end
end DefocusingNLS

end OAI

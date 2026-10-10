import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymmetryGenerator

namespace OAI

/-! # Real stable coordinates induced by the actual complex contour projection -/

open Set
open scoped NNReal

namespace DefocusingNLS

section

variable (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)

local notation "H" => HomogeneousY a k
local notation "J" => homogeneousConjugation a k ha ha1 hk

noncomputable def homogeneousComplexEmbed : H →L[ℝ] H × H :=
  (ContinuousLinearMap.id ℝ H).prod J

@[simp] theorem homogeneousComplexEmbed_apply (u : H) :
    homogeneousComplexEmbed a k ha ha1 hk u = (u, J u) := rfl

@[simp] theorem homogeneousComplexEmbed_norm (u : H) :
    ‖homogeneousComplexEmbed a k ha ha1 hk u‖ = ‖u‖ := by
  simp only [homogeneousComplexEmbed_apply, Prod.norm_def, homogeneousConjugation_norm, max_self]

@[simp] theorem homogeneousComplexReal_embed (u : H) :
    homogeneousComplexReal a k ha ha1 hk (homogeneousComplexEmbed a k ha ha1 hk u) = u := by
  simp only [homogeneousComplexEmbed_apply, homogeneousComplexReal_apply,
    homogeneousConjugation_involutive]
  module

@[simp] theorem homogeneousComplexImag_embed (u : H) :
    homogeneousComplexImag a k ha ha1 hk (homogeneousComplexEmbed a k ha ha1 hk u) = 0 := by
  simp only [homogeneousComplexEmbed_apply, homogeneousComplexImag_apply,
    homogeneousConjugation_involutive, sub_self, smul_zero]

theorem homogeneousComplexification_embed (A : H →L[ℝ] H) (u : H) :
    homogeneousComplexification a k ha ha1 hk A (homogeneousComplexEmbed a k ha ha1 hk u) =
      homogeneousComplexEmbed a k ha ha1 hk (A u) := by
  rw [homogeneousComplexification_apply, homogeneousComplexReal_embed,
    homogeneousComplexImag_embed]
  simp only [map_zero, smul_zero, add_zero, homogeneousComplexEmbed_apply]

noncomputable def homogeneousStableCoordinates (P : (H × H) →L[ℂ] H × H) :
    H →L[ℝ] P.range :=
  (P.rangeRestrict.restrictScalars ℝ).comp (homogeneousComplexEmbed a k ha ha1 hk)

theorem homogeneousStableCoordinates_zero_iff (P : (H × H) →L[ℂ] H × H) (u : H) :
    homogeneousStableCoordinates a k ha ha1 hk P u = 0 ↔
      P (homogeneousComplexEmbed a k ha ha1 hk u) = 0 := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem homogeneousStableCoordinates_decay (b : ℝ) (m : ℕ) (q : H)
    (P : (H × H) →L[ℂ] H × H) (D δ : ℝ)
    (hdecay : ∀ s : ℝ≥0, ∀ u, P u = 0 →
      ‖homogeneousComplexLinearizedStep a b k ha ha1 hk m q s u‖ ≤
        D * Real.exp (-δ * (s : ℝ)) * ‖u‖)
    (T : ℝ) (hT : 0 ≤ T) (u : H)
    (hu : homogeneousStableCoordinates a k ha ha1 hk P u = 0) (t : Icc (0 : ℝ) T) :
    ‖homogeneousLinearizedTrajectory a b k T ha ha1 hk hT m q u t‖ ≤
      D * Real.exp (-δ * (t : ℝ)) * ‖u‖ := by
  have h := hdecay ⟨t, t.2.1⟩ (homogeneousComplexEmbed a k ha ha1 hk u)
    ((homogeneousStableCoordinates_zero_iff a k ha ha1 hk P u).mp hu)
  change ‖homogeneousComplexification a k ha ha1 hk
    (homogeneousLinearizedStep a b k ha ha1 hk m q ⟨t, t.2.1⟩)
    (homogeneousComplexEmbed a k ha ha1 hk u)‖ ≤
      D * Real.exp (-δ * (t : ℝ)) * ‖homogeneousComplexEmbed a k ha ha1 hk u‖ at h
  rw [homogeneousComplexification_embed,
    homogeneousComplexEmbed_norm, homogeneousComplexEmbed_norm,
    homogeneousLinearizedStep_eq_slab a b k ha ha1 hk m q T hT ⟨t, t.2.1⟩ t.2.2] at h
  exact h

end

end DefocusingNLS

end OAI

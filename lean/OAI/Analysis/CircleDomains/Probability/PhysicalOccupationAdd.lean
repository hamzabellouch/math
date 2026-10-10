import OAI.Analysis.CircleDomains.Selection.PhysicalSubpaths
import OAI.Analysis.CircleDomains.Probability.PathPortionMeasure
import OAI.Analysis.CircleDomains.Probability.RectifiableOccupationCode

namespace OAI

/-! Physical arclength occupation is independent of the chosen compact
restriction and adds across a subdivision of the same physical path. -/

open Set MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

omit [BorelSpace Y] in
theorem physicalSubpath_occupation_portion (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b)
    (hγ : BoundedVariationOn (physicalSubpath e hab γ) univ) :
    rectifiableOccupationCode (physicalSubpath e hab γ) =
      pathPortionOccupation ⟨physicalSubpath e hab γ, hγ⟩ a b := by
  rw [rectifiableOccupationCode_eq hγ, ← pathOccupation_clipped _ hab]
  congr 1
  apply Subtype.ext
  exact (physicalSubpath_comp_clip e hab γ).symm

theorem physicalSubpath_occupation_add (e : G ≃ₜ U)
    {a b c : PathTime} (hab : a ≤ b) (hbc : b ≤ c) (γ : C(PathTime, X))
    (hγ : γ ∈ pathsInsideOn U a c)
    (h₁ : γ ∈ pathsInsideOn U a b) (h₂ : γ ∈ pathsInsideOn U b c)
    (hwhole : BoundedVariationOn (physicalSubpath e (hab.trans hbc) ⟨γ, hγ⟩) univ)
    (hleft : BoundedVariationOn (physicalSubpath e hab ⟨γ, h₁⟩) univ)
    (hright : BoundedVariationOn (physicalSubpath e hbc ⟨γ, h₂⟩) univ) :
    rectifiableOccupationCode (physicalSubpath e (hab.trans hbc) ⟨γ, hγ⟩) =
      rectifiableOccupationCode (physicalSubpath e hab ⟨γ, h₁⟩) +
      rectifiableOccupationCode (physicalSubpath e hbc ⟨γ, h₂⟩) := by
  let whole : RectifiablePath Y := ⟨physicalSubpath e (hab.trans hbc) ⟨γ, hγ⟩, hwhole⟩
  let left : RectifiablePath Y := ⟨physicalSubpath e hab ⟨γ, h₁⟩, hleft⟩
  let right : RectifiablePath Y := ⟨physicalSubpath e hbc ⟨γ, h₂⟩, hright⟩
  have hl : EqOn whole.val left.val (Icc a b) := by
    intro t ht
    exact physicalSubpath_eq_on e (hab.trans hbc) hab γ hγ h₁
      ⟨ht.1, ht.2.trans hbc⟩ ht
  have hr : EqOn whole.val right.val (Icc b c) := by
    intro t ht
    exact physicalSubpath_eq_on e (hab.trans hbc) hbc γ hγ h₂
      ⟨hab.trans ht.1, ht.2⟩ ht
  rw [physicalSubpath_occupation_portion e (hab.trans hbc) _ hwhole,
    pathPortionOccupation_add _ hab hbc,
    pathPortionOccupation_congr whole left hab hl,
    pathPortionOccupation_congr whole right hbc hr,
    ← physicalSubpath_occupation_portion e hab _ hleft,
    ← physicalSubpath_occupation_portion e hbc _ hright]

end CircleDomainRigidity

end

end OAI

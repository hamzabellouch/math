import OAI.Analysis.CoulombTransport.FiveComponentGeometry
import OAI.Analysis.CoulombTransport.ContactCommonBranches

namespace OAI

noncomputable section
open Set

namespace Problem356.FiveComponentGeometry

/-- The actual symmetric two-graph contact relation yields the exact selector
needed by the final construction. Graph-wide outer exclusions are supplied by
`CoulombSupportExistence.exists_separated_shrink`; the final central ball can
be any subset of the excluded central neighborhood. -/
theorem second_selects_four_of_excluded_charts
    (C₁ : ChartsAt (CenterCertificate.point 1))
    (C₂ : ChartsAt (CenterCertificate.point 3))
    {B V : Set E3} (hB : B ⊆ V)
    (houter₁ : ∀ s ∈ C₁.charts.central.source, s ∉ V ∧ C₁.charts.opposite s ∉ V)
    (houter₂ : ∀ s ∈ C₂.charts.central.source, s ∉ V ∧ C₂.charts.opposite s ∉ V)
    {x y z : E3} (hx : x ∈ B) (hc : branchContact C₁ C₂ (x, (y, z))) :
    ∃ i : Fin 4, y = CommonBranches.four
      ![C₁.charts.central, C₂.charts.central]
      ![C₁.charts.opposite, C₂.charts.opposite] i x := by
  rcases hc with ⟨s, hs, hp⟩ | ⟨s, hs, hp⟩
  · have ho := houter₁ s hs
    exact ContactSelection.second_selects_common_four _ _ (k := 0) hp hx hs
      (fun h => ho.1 (hB h)) (fun h => ho.2 (hB h))
  · have ho := houter₂ s hs
    exact ContactSelection.second_selects_common_four _ _ (k := 1) hp hx hs
      (fun h => ho.1 (hB h)) (fun h => ho.2 (hB h))

end Problem356.FiveComponentGeometry

end

end OAI

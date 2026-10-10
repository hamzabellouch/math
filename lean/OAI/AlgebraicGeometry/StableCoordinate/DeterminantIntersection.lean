import OAI.AlgebraicGeometry.StableCoordinate.ChartIntersection
import OAI.AlgebraicGeometry.StableCoordinate.DeterminantCharts
import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDomains

namespace OAI

/-!
# The actual coefficient-ring intersection for the determinant hypersurface

This is the two-chart coefficient-membership step in source Section 5, now
instantiated on the exact quotient `k[a,d,b,c,u]/(ac-bd-1)`.  The chart maps,
their injectivity, the domain property, and independence of `a,d,u` are all
proved constructions.  No chart or domain assumption remains in the theorems.
-/

namespace StableCoordinate.DeterminantRing

open MvPolynomial

variable (k : Type*) [Field k]

/-- If an element of the determinant ring is a coefficient in each of its two
polynomial charts, it belongs to the actual polynomial subring `k[a,d,u]`. -/
theorem exists_base_of_constant_charts {q : C k}
    {v : BaseAway k 0} {w : BaseAway k 1}
    (hA : chartMapA k q = Polynomial.C v)
    (hD : chartMapD k q = Polynomial.C w) :
    ∃ r : Base k, baseMap r = q := by
  exact ChartIntersection.exists_base_of_two_ring_charts
    (baseMap (k := k)).toRingHom (MvPolynomial.X_ne_zero (0 : Fin 3))
    (StableCoordinate.isRelPrime_X_of_ne (k := k) (i := (0 : Fin 3))
      (j := (1 : Fin 3)) (by decide))
    (chartMapA k).toRingHom (chartMapA_injective k)
    (chartMapD k).toRingHom (chartMapD_injective k)
    (chartMapA_baseMap k) (chartMapD_baseMap k) hA hD

/-- Exact membership characterization, with both implications retained. -/
theorem mem_range_baseMap_iff_constant_charts (q : C k) :
    q ∈ Set.range (baseMap (k := k)) ↔
      (∃ v : BaseAway k 0, chartMapA k q = Polynomial.C v) ∧
      (∃ w : BaseAway k 1, chartMapD k q = Polynomial.C w) := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨⟨_, chartMapA_baseMap k r⟩, ⟨_, chartMapD_baseMap k r⟩⟩
  · rintro ⟨⟨v, hA⟩, ⟨w, hD⟩⟩
    exact exists_base_of_constant_charts k hA hD

end StableCoordinate.DeterminantRing

end OAI

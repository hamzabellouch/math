import OAI.MeasureTheory.Falconer.Shells.TwoRootMasks

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem restoredTwoRootMask_one_outside (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane)
    (hx : z.1 ∈ retainedClassUnion Q₀ μ N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))))
    (hy : z.2 ∈ retainedClassUnion Q₁ ν N B₂ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))))
    (hf₁ : sourceRadialUnit z.1 z.2 ∉ retainedAngularFailure Q₀ μ m₁ N B₁ lam sig kap z.1)
    (hf₂ : sourceRadialUnit z.2 z.1 ∉ retainedAngularFailure Q₁ ν m₂ N B₂ lam sig kap z.2) :
    restoredTwoRootMask Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β z = 1 := by
  obtain ⟨T,hT,hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨U,hU,hy⟩ := mem_iUnion₂.mp hy
  rw [restoredTwoRootMask_on_pair Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β (a := (T,U)) (z := z) (Finset.mem_product.mpr ⟨hT,hU⟩) ⟨hx,hy⟩]
  let c := outerEntry (m₁ T) (m₂ U) N β
  have hc : c ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (outerEntry_le _ _ _ _))
  have h₁ : outerEndpointMask Q₀ (actualClassMeasure Q₀ μ N B₁ T) (m₁ T) N lam sig kap c z.1 (sourceRadialUnit z.1 z.2) = 1 := by
    by_contra hn
    exact hf₁ (mem_iUnion₂.mpr ⟨T,hT,hx,mem_iUnion₂.mpr ⟨c,hc,hn⟩⟩)
  have h₂ : outerEndpointMask Q₁ (actualClassMeasure Q₁ ν N B₂ U) (m₂ U) N lam sig kap c z.2 (sourceRadialUnit z.1 z.2) = 1 := by
    by_contra hn
    apply hf₂
    refine mem_iUnion₂.mpr ⟨U,hU,hy,mem_iUnion₂.mpr ⟨c,hc,?_⟩⟩
    simpa only [Set.mem_ofPred_eq,outerEndpointMask_radial_swap] using hn
  change ENNReal.ofReal (outerEndpointMask Q₀ (actualClassMeasure Q₀ μ N B₁ T) (m₁ T) N lam sig kap c z.1 (sourceRadialUnit z.1 z.2)*
    outerEndpointMask Q₁ (actualClassMeasure Q₁ ν N B₂ U) (m₂ U) N lam sig kap c z.2 (sourceRadialUnit z.1 z.2)) = 1
  rw [h₁,h₂,mul_one,ENNReal.ofReal_one]

end PlanarFalconer

end OAI

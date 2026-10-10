import OAI.MeasureTheory.Falconer.Angular.RetainedAngularFailure
import OAI.MeasureTheory.Falconer.Recursion.DescriptorMaskSymmetry

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem sourceRadialUnit_swap {x y : Plane} (hxy : x ≠ y) :
    sourceRadialUnit y x = circleAntipode (sourceRadialUnit x y) := by
  apply Subtype.ext
  change sourceRadialVector y x = -sourceRadialVector x y
  simp only [sourceRadialVector,ite_eq_right hxy,ite_eq_right hxy.symm]
  rw [← neg_sub y x,norm_neg,smul_neg]

theorem outerEndpointMask_radial_swap (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) (c : ℕ) (z x y : Plane) :
    outerEndpointMask Q ρ m N lam sig kap c z (sourceRadialUnit y x) =
      outerEndpointMask Q ρ m N lam sig kap c z (sourceRadialUnit x y) := by
  by_cases hxy : x = y
  · subst y; rfl
  · rw [sourceRadialUnit_swap hxy]
    exact descriptorListMask_antipodal _ _ _ _ _ _ _ _ _ _ _

theorem outerEntry_comm (m₁ m₂ : ℝ → ℝ) (N : ℕ) (β : ℝ) :
    outerEntry m₁ m₂ N β = outerEntry m₂ m₁ N β := by
  simp only [outerEntry,min_comm]

theorem restoredShellMask_one_outside (Q : DyadicSquare) (hQ : 0 < Q.side) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane)
    (hx : z.1 ∈ retainedClassUnion Q μ N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))))
    (hy : z.2 ∈ retainedClassUnion Q ν N B₂ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))))
    (hf₁ : sourceRadialUnit z.1 z.2 ∉ retainedAngularFailure Q μ m₁ N B₁ lam sig kap z.1)
    (hf₂ : sourceRadialUnit z.2 z.1 ∉ retainedAngularFailure Q ν m₂ N B₂ lam sig kap z.2) :
    restoredShellMask Q μ ν m₁ m₂ N B₁ B₂ lam sig kap β z = 1 := by
  obtain ⟨T,hT,hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨U,hU,hy⟩ := mem_iUnion₂.mp hy
  rw [restoredShellMask_on_pair Q hQ μ ν m₁ m₂ N B₁ B₂ lam sig kap β (a := (T,U)) (z := z) (Finset.mem_product.mpr ⟨hT,hU⟩) hx hy]
  let c := outerEntry (m₁ T) (m₂ U) N β
  have hc : c ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (outerEntry_le _ _ _ _))
  have h₁ : outerEndpointMask Q (actualClassMeasure Q μ N B₁ T) (m₁ T) N lam sig kap c z.1 (sourceRadialUnit z.1 z.2) = 1 := by
    by_contra hn
    exact hf₁ (mem_iUnion₂.mpr ⟨T,hT,hx,mem_iUnion₂.mpr ⟨c,hc,hn⟩⟩)
  have h₂ : outerEndpointMask Q (actualClassMeasure Q ν N B₂ U) (m₂ U) N lam sig kap c z.2 (sourceRadialUnit z.1 z.2) = 1 := by
    by_contra hn
    apply hf₂
    refine mem_iUnion₂.mpr ⟨U,hU,hy,mem_iUnion₂.mpr ⟨c,hc,?_⟩⟩
    simpa only [Set.mem_ofPred_eq,outerEndpointMask_radial_swap] using hn
  change ENNReal.ofReal (outerEndpointMask Q (actualClassMeasure Q μ N B₁ T) (m₁ T) N lam sig kap c z.1 (sourceRadialUnit z.1 z.2)*
    outerEndpointMask Q (actualClassMeasure Q ν N B₂ U) (m₂ U) N lam sig kap c z.2 (sourceRadialUnit z.1 z.2)) = 1
  rw [h₁,h₂,mul_one,ENNReal.ofReal_one]

end PlanarFalconer

end OAI

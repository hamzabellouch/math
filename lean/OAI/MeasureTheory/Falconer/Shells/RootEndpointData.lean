import OAI.MeasureTheory.Falconer.Fourier.MinimalPairSymbol
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks
import OAI.MeasureTheory.Falconer.Recursion.MinimalDescriptorLength

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

structure RootEndpointData where
  Q : DyadicSquare
  ρ : Measure Plane
  mass : ℝ → ℝ
  lam : ℝ
  J : ℕ
  i : ℕ
  S : Finset PolicyDescriptor

namespace RootEndpointData

noncomputable def mask (d : RootEndpointData) (N : ℕ) (sig : ℝ) : Plane → UnitCircle → ℝ :=
  descriptorListMask d.Q d.ρ d.mass N d.lam sig d.J d.i d.S

noncomputable def symbol (d : RootEndpointData) (N : ℕ) (sig : ℝ)
    (k : PolicyDescriptor → ℕ) (h : Plane → ℂ) : Plane → UnitCircle → ℂ :=
  inheritedCircleSymbol d.S id k d.Q d.ρ d.mass N d.lam sig d.J d.i h

theorem symbol_zero (d : RootEndpointData) (N : ℕ) (sig : ℝ) (x : Plane) (dir : UnitCircle) :
    d.symbol N sig (fun _ => 0) (fun _ => 1) x dir = (d.mask N sig x dir : ℂ) :=
  inheritedCircleSymbol_zero_assignment _ _ _ _ _ _ _ _ _ _ _

theorem mask_bounds (d : RootEndpointData) (hQ : 0 < d.Q.side)
    (N : ℕ) (sig : ℝ) (x : Plane) (dir : UnitCircle) :
    0 ≤ d.mask N sig x dir ∧ d.mask N sig x dir ≤ 1 :=
  descriptorListMask_bounds _ hQ _ _ _ _ _ _ _ _ _ _

theorem mask_measurable (d : RootEndpointData) (N : ℕ) (sig : ℝ) :
    Measurable (fun z : Plane × UnitCircle => d.mask N sig z.1 z.2) :=
  measurable_descriptorListMask _ _ _ _ _ _ _ _ _

noncomputable def ofOuter (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig kap : ℝ) (c : ℕ) : RootEndpointData :=
  ⟨Q,ρ,m,lam,sourceSmoothingLevels sig kap,0,
    outerDescriptorList m N (sourcePolicyBlock N kap) c⟩

theorem ofOuter_mask (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig kap : ℝ) (c : ℕ) :
    (ofOuter Q ρ m N lam sig kap c).mask N sig =
      outerEndpointMask Q ρ m N lam sig kap c := rfl

end RootEndpointData

theorem outerDescriptorList_length (m : ℝ → ℝ) {N q c : ℕ}
    (hq : 0 < q) {b : PolicyDescriptor} (hb : b ∈ outerDescriptorList m N q c) :
    descriptorLength b ≤ max c ((N-c)/2) := by
  obtain rfl | hb := Finset.mem_insert.mp hb
  · simp [descriptorLength]
  · exact (policyDescriptor_length_le_half _ hq hb).trans (le_max_right _ _)

theorem outerDescriptorList_half (m : ℝ → ℝ) {N q c : ℕ}
    (hq : 0 < q) (hc : 2*c ≤ N) {b : PolicyDescriptor}
    (hb : b ∈ outerDescriptorList m N q c) : descriptorLength b ≤ N/2 := by
  exact (outerDescriptorList_length m hq hb).trans (max_le (by omega) (by omega))

end PlanarFalconer

end OAI

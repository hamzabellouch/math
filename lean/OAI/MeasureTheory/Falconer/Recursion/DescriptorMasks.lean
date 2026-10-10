import OAI.MeasureTheory.Falconer.Estimates.SpatialAnchorMasks
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

def ValidDescriptor (N : ℕ) : PolicyDescriptor → Prop
  | .parallel g p => g ≤ p ∧ p ≤ N
  | .projection p u => p ≤ u ∧ u ≤ N

noncomputable def descriptorGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) : PolicyDescriptor → Set UnitCircle
  | .parallel g p => parallelGoodSet Q ρ g p P (sourceAngularWidth N sig J i p)
      (((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+2000*(lam+sig)))
  | .projection p u => projectionGoodSet Q ρ p u P (sourceAngularWidth N sig J i u)
      (((2:ℝ)^N)^(m u-m p+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+2000*(lam+sig)))

noncomputable def descriptorSpatialMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) : Plane → UnitCircle → ℝ :=
  spatialAnchorMask Q ρ (descriptorAnchor b) (fun P => descriptorGoodSet Q ρ m N lam sig J i P b)
    (sourceAngularRadius N sig (descriptorLength b)) (sourceAngularRadius_pos _ _ _)

noncomputable def descriptorListMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (S : Finset PolicyDescriptor)
    (x : Plane) (dir : UnitCircle) : ℝ :=
  ∏ b ∈ S, descriptorSpatialMask Q ρ m N lam sig J i b x dir

theorem measurable_descriptorGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (b : PolicyDescriptor) :
    MeasurableSet (descriptorGoodSet Q ρ m N lam sig J i P b) := by
  cases b with
  | parallel g p => exact measurable_parallelGoodSet _ _ _ _ _ _ _
  | projection p u => exact measurable_projectionGoodSet _ _ _ _ _ _ _

theorem descriptorSpatialMask_bounds (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) (dir : UnitCircle) :
    0 ≤ descriptorSpatialMask Q ρ m N lam sig J i b x dir ∧
      descriptorSpatialMask Q ρ m N lam sig J i b x dir ≤ 1 := spatialAnchorMask_bounds Q hQ _ _ _ _ _ _ _

@[fun_prop] theorem measurable_descriptorSpatialMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) :
    Measurable (fun z : Plane × UnitCircle => descriptorSpatialMask Q ρ m N lam sig J i b z.1 z.2) :=
  measurable_spatialAnchorMask _ _ _ _ _ _

@[fun_prop] theorem measurable_descriptorListMask (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (S : Finset PolicyDescriptor) :
    Measurable (fun z : Plane × UnitCircle => descriptorListMask Q ρ m N lam sig J i S z.1 z.2) := by
  apply Finset.measurable_prod
  intro b _
  exact measurable_descriptorSpatialMask _ _ _ _ _ _ _ _ _

theorem descriptorListMask_bounds (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (S : Finset PolicyDescriptor) (x : Plane) (dir : UnitCircle) :
    0 ≤ descriptorListMask Q ρ m N lam sig J i S x dir ∧
      descriptorListMask Q ρ m N lam sig J i S x dir ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun b _ => (descriptorSpatialMask_bounds Q hQ ρ m N lam sig J i b x dir).1)
  · exact Finset.prod_le_one₀ (fun b _ => (descriptorSpatialMask_bounds Q hQ ρ m N lam sig J i b x dir).1)
      (fun b _ => (descriptorSpatialMask_bounds Q hQ ρ m N lam sig J i b x dir).2)

theorem descriptorGoodSet_exceptional (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J : ℕ)
    (ha : SourceAngularBounds Q ρ m N lam sig) {b : PolicyDescriptor} (hb : ValidDescriptor N b)
    {P : CellPath} (hP : P.length = descriptorAnchor b) :
    sourceArcLength (descriptorGoodSet Q ρ m N lam sig J 0 P b)ᶜ ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  cases b with
  | parallel g p => simpa only [descriptorGoodSet,sourceAngularWidth_zero] using ha.parallel g p hb.1 hb.2 P hP
  | projection p u => simpa only [descriptorGoodSet,sourceAngularWidth_zero] using ha.projection p u hb.1 hb.2 P hP

theorem policyDescriptor_valid (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N)
    {b : PolicyDescriptor} (hb : b ∈ policyDescriptorList A N q a t) : ValidDescriptor N b := by
  obtain ⟨s,u,_,hut,_,_,hpos,_,hbound⟩ := policyDescriptor_origin A hq hb
  cases b <;> simp only [descriptorLength,descriptorAnchor,ValidDescriptor] at hpos hbound ⊢ <;> omega

end PlanarFalconer

end OAI

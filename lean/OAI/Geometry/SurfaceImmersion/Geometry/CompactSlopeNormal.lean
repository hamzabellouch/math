import OAI.Geometry.SurfaceImmersion.Primitive.CompactCrossingNormal
import OAI.Geometry.SurfaceImmersion.Primitive.CrossingInvariantScaling

namespace OAI

/-! Construct the actual preferred normal from the slope-coordinate
estimates, retaining both ordered invariants in the original directions. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem compact_slope_crossing_normal {F : RField 4} (hF : ContDiff ℝ ∞ F) (z : ℝ)
    {T V : Set Base} (hV : IsOpen V)
    (hreg : ∀ p ∈ T, realBoundaryProfile F z p ∈ regularBoundaryProfiles)
    (Y : κ → Base → Base) (hY : ∀ k, ContDiff ℝ ∞ (Y k))
    (left right : ι → κ) (x : ι → Base) (hxinj : Function.Injective x)
    (hxT : ∀ i, x i ∈ T) (hxV : ∀ i, x i ∈ V)
    (C : κ → Set Base) (hC : ∀ k, IsClosed (C k))
    (honly : ∀ i k, x i ∈ C k → k = left i ∨ k = right i)
    (havoid : ∀ k p, p ∈ T → p ∈ C k →
      normalize (realSecondForm F (Y k p) (Y k p) p) ≠ -profilePreferred (realBoundaryProfile F z p))
    (hv : ∀ i, (Y (left i) (x i)).1 ≠ 0 ∧ (Y (right i) (x i)).1 ≠ 0)
    (d : ℝ) (hd : ∀ i, |(Y (left i) (x i)).2/(Y (left i) (x i)).1| ≤ d ∧
      |(Y (right i) (x i)).2/(Y (right i) (x i)).1| ≤ d)
    (curv : Base → ℝ)
    (hcross : ∀ i, ∀ r s : ℝ, |r| ≤ d → |s| ≤ d →
      0 < orderedCrossing F (1,r) (1,s) (x i) (curv (x i)) ∧
      0 < orderedCrossing F (1,s) (1,r) (x i) (curv (x i)) ∧
      ((0 < realSecondForm F (1,r) (1,r) (x i) ⬝ᵥ profilePreferred (realBoundaryProfile F z (x i)) ∧
        0 < realSecondForm F (1,s) (1,s) (x i) ⬝ᵥ profilePreferred (realBoundaryProfile F z (x i))) ∨
       (0 < realSecondForm F (1,r) (1,r) (x i) ⬝ᵥ realSecondForm F (1,s) (1,s) (x i) ∧
        ∃ w : Vec, profilePreferred (realBoundaryProfile F z (x i)) ⬝ᵥ w = 0 ∧
          0 < realSecondForm F (1,r) (1,r) (x i) ⬝ᵥ w ∧
          0 < realSecondForm F (1,s) (1,s) (x i) ⬝ᵥ w))) :
    ∃ U : Set Base, IsOpen U ∧ T ⊆ U ∧ ∃ g : Base → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ p ∈ U, g p ⬝ᵥ g p = 1) ∧
      (∀ p ∈ U, ∀ v : Base, coordDeriv v F p ⬝ᵥ g p = 0) ∧
      (∀ p ∈ U, p ∉ V → g p = profilePreferred (realBoundaryProfile F z p)) ∧
      (∀ k p, p ∈ T → p ∈ C k → g p ≠ -normalize (realSecondForm F (Y k p) (Y k p) p)) ∧
      ∀ i,
        0 < orderedCrossing F (Y (left i) (x i)) (Y (right i) (x i)) (x i) (curv (x i)) ∧
        0 < orderedCrossing F (Y (right i) (x i)) (Y (left i) (x i)) (x i) (curv (x i)) ∧
        0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ g (x i) ∧
        0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ g (x i) := by
  have hdata (i : ι) := hcross i _ _ (hd i).1 (hd i).2
  obtain ⟨U,hU,hTU,g,hg,hunit,hnormal,hout,havoid',hpos⟩ := compact_actual_crossing_normal
    hF z hV hreg Y hY left right x hxinj hxT hxV C hC honly havoid
    (fun i => crossing_choice_firstSlope hF (x i) (profilePreferred (realBoundaryProfile F z (x i)))
      _ _ (hv i).1 (hv i).2 (hdata i).2.2)
  refine ⟨U,hU,hTU,g,hg,hunit,hnormal,hout,havoid',?_⟩
  intro i
  have hp := mul_pos (sq_pos_of_ne_zero (hv i).1) (sq_pos_of_ne_zero (hv i).2)
  refine ⟨?_,?_,(hpos i).1,(hpos i).2⟩
  · rw [orderedCrossing_firstSlope hF _ _ _ _ (hv i).1 (hv i).2]
    exact mul_pos hp (hdata i).1
  · rw [orderedCrossing_firstSlope hF _ _ _ _ (hv i).2 (hv i).1]
    exact mul_pos (by simpa [mul_comm] using hp) (hdata i).2.1

end ClosedSurfaceR4.GeometryPreservation

end

end OAI

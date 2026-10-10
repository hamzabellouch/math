import OAI.Geometry.SurfaceImmersion.Primitive.CompactCrossingChoice
import OAI.Geometry.SurfaceImmersion.Primitive.ActualFiniteCrossingNormal

namespace OAI

/-! Turn regularity on a compact disk and finitely many actual crossing
choices into one smooth normal on an open neighborhood of the disk. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem compact_actual_crossing_normal {F : RField 4} (hF : ContDiff ℝ ∞ F) (z : ℝ)
    {T V : Set Base} (hV : IsOpen V)
    (hreg : ∀ p ∈ T, realBoundaryProfile F z p ∈ regularBoundaryProfiles)
    (Y : κ → Base → Base) (hY : ∀ k, ContDiff ℝ ∞ (Y k))
    (left right : ι → κ) (x : ι → Base) (hxinj : Function.Injective x)
    (hxT : ∀ i, x i ∈ T) (hxV : ∀ i, x i ∈ V)
    (C : κ → Set Base) (hC : ∀ k, IsClosed (C k))
    (honly : ∀ i k, x i ∈ C k → k = left i ∨ k = right i)
    (havoid : ∀ k p, p ∈ T → p ∈ C k →
      normalize (realSecondForm F (Y k p) (Y k p) p) ≠ -profilePreferred (realBoundaryProfile F z p))
    (hchoice : ∀ i,
      (0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ
          profilePreferred (realBoundaryProfile F z (x i)) ∧
       0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ
          profilePreferred (realBoundaryProfile F z (x i))) ∨
      (0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ
          realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ∧
        ∃ w : Vec, profilePreferred (realBoundaryProfile F z (x i)) ⬝ᵥ w = 0 ∧
          0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ w ∧
          0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ w)) :
    ∃ U : Set Base, IsOpen U ∧ T ⊆ U ∧ ∃ g : Base → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ p ∈ U, g p ⬝ᵥ g p = 1) ∧
      (∀ p ∈ U, ∀ v : Base, coordDeriv v F p ⬝ᵥ g p = 0) ∧
      (∀ p ∈ U, p ∉ V → g p = profilePreferred (realBoundaryProfile F z p)) ∧
      (∀ k p, p ∈ T → p ∈ C k → g p ≠ -normalize (realSecondForm F (Y k p) (Y k p) p)) ∧
      ∀ i, 0 < realSecondForm F (Y (left i) (x i)) (Y (left i) (x i)) (x i) ⬝ᵥ g (x i) ∧
        0 < realSecondForm F (Y (right i) (x i)) (Y (right i) (x i)) (x i) ⬝ᵥ g (x i) := by
  let U := realBoundaryProfile F z ⁻¹' regularBoundaryProfiles
  have hU : IsOpen U := isOpen_regularBoundaryProfiles.preimage (realBoundaryProfile_smooth hF z).continuous
  have hTU : T ⊆ U := hreg
  obtain ⟨g,hg,hunit,hnormal,hout,havoid',hpos⟩ := actual_finite_crossing_normal hF z hV
    (fun _ hp => hp) Y (fun k => (hY k).contDiffOn) left right x hxinj
    (fun i => hTU (hxT i)) hxV C hC honly hchoice hU
  refine ⟨U,hU,hTU,g,hg,hunit,hnormal,hout,?_,hpos⟩
  intro k p hpT hpC
  apply havoid' k p (hTU hpT) hpC
  intro hbad
  apply havoid k p hpT hpC
  rw [hbad,neg_neg]

end ClosedSurfaceR4.GeometryPreservation

end

end OAI

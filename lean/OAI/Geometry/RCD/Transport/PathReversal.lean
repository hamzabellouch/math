import OAI.Analysis.RCDHeat.CompressionIntegral
import OAI.Geometry.RCD.Transport.PathAgreement

namespace OAI

/-! # Time reversal and final-interval agreement -/

open Set
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

@[simp] theorem timeSegment_one_zero_coe (t : Time) : (timeSegment 1 0 t:ℝ)=1-(t:ℝ) := by
  simp [timeSegment]

@[simp] theorem timeSegment_reverse_reverse (t : Time) :
    timeSegment 1 0 (timeSegment 1 0 t)=t := by
  apply Subtype.ext
  simp

@[simp] theorem subpath_reverse_reverse (γ : C(Time,X)) : subpath 1 0 (subpath 1 0 γ)=γ := by
  ext t
  change γ (timeSegment 1 0 (timeSegment 1 0 t))=γ t
  rw [timeSegment_reverse_reverse]

theorem subpath_reverse_injective : Function.Injective (subpath (X:=X) 1 0) := by
  intro γ ζ he
  have h := congrArg (subpath 1 0) he
  simpa only [subpath_reverse_reverse] using h

theorem reversed_pair_agreement (q : Time) (γ ζ : C(Time,X))
    (he : ∀ r : Time, q ≤ r → γ r=ζ r) :
    (subpath 1 0 γ,subpath 1 0 ζ) ∈ pathAgreement (1-(q:ℝ)) := by
  intro r hr
  apply he
  change (q:ℝ) ≤ (timeSegment 1 0 r:ℝ)
  rw [timeSegment_one_zero_coe]
  linarith

end RegularPointCoordinates

end OAI

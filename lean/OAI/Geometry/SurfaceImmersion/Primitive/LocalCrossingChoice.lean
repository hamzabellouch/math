import OAI.Geometry.SurfaceImmersion.Primitive.LocalCrossingAdjustment

namespace OAI

/-! The pointwise turn alternative supplies the actual supported normal
adjustment, including the case where the original normal already works. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem local_crossing_adjustment_of_choice {U O : Set E} (hU : IsOpen U) (hO : IsOpen O)
    {n p q : E → Vec} (hn : ContDiffOn ℝ ∞ n U)
    (hp : ContDiffOn ℝ ∞ p U) (hq : ContDiffOn ℝ ∞ q U)
    (hunit : ∀ y ∈ U, n y ⬝ᵥ n y = 1) {x : E} (hx : x ∈ U) (hxO : x ∈ O)
    (hchoice : (0 < p x ⬝ᵥ n x ∧ 0 < q x ⬝ᵥ n x) ∨
      (0 < p x ⬝ᵥ q x ∧ ∃ w : Vec, n x ⬝ᵥ w = 0 ∧
        0 < p x ⬝ᵥ w ∧ 0 < q x ⬝ᵥ w)) :
    ∃ g : E → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ y ∈ U, g y ⬝ᵥ g y = 1) ∧
      (∀ y ∈ U, y ∉ O → g y = n y) ∧
      (∀ y ∈ U, n y ≠ -normalize (p y) → g y ≠ -normalize (p y)) ∧
      (∀ y ∈ U, n y ≠ -normalize (q y) → g y ≠ -normalize (q y)) ∧
      (∀ y ∈ U, ∀ v : Vec, v ⬝ᵥ n y = 0 → v ⬝ᵥ p y = 0 → v ⬝ᵥ g y = 0) ∧
      0 < p x ⬝ᵥ g x ∧ 0 < q x ⬝ᵥ g x := by
  rcases hchoice with hpos | ⟨hpq,w,hnw,hpw,hqw⟩
  · exact ⟨n,hn,hunit,fun _ _ _ => rfl,fun _ _ h => h,fun _ _ h => h,
      fun _ _ _ h _ => h,hpos⟩
  · exact local_crossing_adjustment hU hO hn hp hq hunit hx hxO hnw hpw hqw hpq

end ClosedSurfaceR4.VelocityFrame

end

end OAI

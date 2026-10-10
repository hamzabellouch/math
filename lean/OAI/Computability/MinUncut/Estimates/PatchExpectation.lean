import Mathlib
import OAI.Computability.MinUncut.Games.HintSimulation

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
attribute [local instance] Classical.propDecidable
variable {I X : Type*} [Fintype I] [Fintype X] [Nonempty X]

lemma expect_le_of_active_sections (A : I → Prop) (f : (I → X) → ℝ) (C : ℝ)
    (h : ∀ bg : I → X, (𝔼 u : {i // A i} → X, f (patch A bg u)) ≤ C) :
    (𝔼 w : I → X, f w) ≤ C := by
  classical
  let bg (v : {i // ¬A i} → X) : I → X :=
    fun i => if hi : ¬A i then v ⟨i,hi⟩ else Classical.ofNonempty
  let e := Equiv.piEquivPiSubtypeProd A (fun _ => X)
  have he : (𝔼 w : I → X, f w) =
      𝔼 z : ({i // A i} → X) × ({i // ¬A i} → X), f (patch A (bg z.2) z.1) := by
    apply Fintype.expect_equiv e
    intro w
    congr 1
    funext i
    by_cases hi : A i <;> simp [patch,bg,e,Equiv.piEquivPiSubtypeProd,hi]
  rw [he,OuterSmoothness.expect_pair,Finset.expect_comm]
  calc
    _ ≤ 𝔼 _ : {i // ¬A i} → X, C := Finset.expect_le_expect (fun v _ => h (bg v))
    _ = C := Fintype.expect_const _

end MinUncut.Outer

end
end

end OAI

import OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Units.Equiv

namespace OAI

/-! Freeze a progression class and change every prime residue by the
same invertible affine map. This preserves the precise uniform model. -/

namespace TwoPointCorrelations

open scoped Classical

lemma uniformAverage_residue_affine {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (a l : ℕ) (hl : ∀ i, l.Coprime (s i)) (F : (∀ i, ZMod (s i)) → ℝ) :
    uniformAverage (fun z : ∀ i, ZMod (s i) =>
      F (fun i => (a : ZMod (s i)) + (l : ZMod (s i)) * z i)) =
      uniformAverage F := by
  let e : (∀ i, ZMod (s i)) ≃ (∀ i, ZMod (s i)) := Equiv.piCongrRight fun i =>
    (Units.mulLeft (ZMod.unitOfCoprime l (hl i))).trans (Equiv.addLeft (a : ZMod (s i)))
  have he (z : ∀ i, ZMod (s i)) : e z =
      fun i => (a : ZMod (s i)) + (l : ZMod (s i)) * z i := by
    funext i
    change (a : ZMod (s i)) + (ZMod.unitOfCoprime l (hl i) : ZMod (s i)) * z i = _
    rw [ZMod.coe_unitOfCoprime]
  simpa only [he] using uniformAverage_equiv e F

end TwoPointCorrelations

end OAI

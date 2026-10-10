import OAI.NumberTheory.Ostmann.Characters.QuartetTreeData
import OAI.NumberTheory.Ostmann.Characters.QuartetLocalBounds
import OAI.NumberTheory.Ostmann.Tree.RationalQuartetCut

namespace OAI

/-! # Local estimates on every depth-two tree arising from the cut -/

namespace Ostmann

open scoped BigOperators

theorem rationalTree_quartet_coefficient_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ 2 C) (XL XR P : (ZMod p)ˣ)
    (cL cR : Bool) (choice : QuartetMovingCase) (ρ : MulChar (ZMod p) ℂ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ a : (ZMod p)ˣ,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ b : (ZMod p)ˣ,
        ‖mellinCoefficient (fun r : (ZMod p)ˣ =>
          rationalTreeAmplitude g D T XL XR ((cL, !cL), (cR, !cR))
            (quartetMovingLeaves choice P a b r)) ρ‖ ^ 2) ≤
      quartetMovingMajorant g cL cR choice ρ (rationalTreeArgument T.frequency C D XL XR P) := by
  obtain ⟨Q, rfl, rfl⟩ := T.exists_quartet
  exact quartetMoving_coefficient_le g D Q XL XR P cL cR choice ρ

theorem rationalTree_quartet_secondMoment_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) {C : (ZMod p)ˣ}
    (T : RationalTreeData (ZMod p)ˣ 2 C) (XL XR P : (ZMod p)ˣ)
    (c : TreeLeafTuple Bool 2) :
    (Fintype.card (TreeLeafFiber (ZMod p)ˣ 2 P) : ℝ)⁻¹ *
      (∑ m : TreeLeafFiber (ZMod p)ˣ 2 P,
        ‖rationalTreeAmplitude g D T XL XR c m.1‖ ^ 2) ≤
      8 * differenceMajorant (fieldPairMoment g) (fieldPairMoment g)
        (rationalTreeArgument T.frequency C D XL XR P) := by
  obtain ⟨Q, rfl, rfl⟩ := T.exists_quartet
  exact rationalQuartet_fiber_secondMoment_le_any_conjugation g D Q XL XR P c

theorem rationalQuartetState_secondMoment_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (D : (ZMod p)ˣ) (S : RationalQuartetState p) (P : (ZMod p)ˣ) :
    (Fintype.card (TreeLeafFiber (ZMod p)ˣ 2 P) : ℝ)⁻¹ *
      (∑ m : TreeLeafFiber (ZMod p)ˣ 2 P, ‖rationalQuartetStateAmplitude g D S m.1‖ ^ 2) ≤
      8 * differenceMajorant (fieldPairMoment g) (fieldPairMoment g)
        (rationalQuartetStateArgument D S P) :=
  rationalTree_quartet_secondMoment_le g D S.tree S.XL S.XR P S.conjugations

end Ostmann

end OAI

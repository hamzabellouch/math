import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.HistoryRecoveryBudget

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCanonicalSymmetry

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open JointCanonicalMixed HistorySymmetry PermutationMatching

attribute [local instance] Classical.propDecidable

variable {H F : Type*} [Fintype H] [DecidableEq H] [CommRing F]
    (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
    (parentShape : H → Fin 3 → ℕ) (sharing : H → Bool)
    (hleft : ∀ h, leftLength h ≤ 8)
    {SL SR : H → Type*}
    [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)]
    [∀ h, DecidableEq (SL h)] [∀ h, DecidableEq (SR h)]
    (sl : Fin 3 → ∀ c : ClassKey (H := H), Left leftLength c.1 → SL c.1)
    (sr : Fin 3 → ∀ c : ClassKey (H := H), Right rightLength c.1 → SR c.1)
    (νl : Fin 3 → ∀ c : ClassKey (H := H), SL c.1 → ℝ)
    (νr : Fin 3 → ∀ c : ClassKey (H := H), SR c.1 → ℝ)
    (ηl ηr : Fin 3 → ClassKey (H := H) → ℝ)
    (hsupport : ∀ h u, 0 < counts h u → sharing h = true →
      ∀ s, shapeNat u s ≤ parentShape h s)

include hsupport

omit [DecidableEq H] [∀ h, Fintype (SL h)] [∀ h, Fintype (SR h)] in
theorem canonicalIdeal_smul
    (g : HalfClassPermutations (ClassPositions counts))
    (x y z : CanonicalPairs counts (Left leftLength) (Right rightLength)) :
    canonicalIdeal counts (Left leftLength) (Right rightLength)
      (inputTensor (F := F) leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr
      (g • x) (g • y) (g • z) =
    canonicalIdeal counts (Left leftLength) (Right rightLength)
      (inputTensor leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr x y z := by
  simp only [canonicalIdeal,
    JointCanonicalMixed.canonicalBase_eq_children counts leftLength rightLength
      parentShape sharing hleft hsupport,
    ExactRecovery.delete, childWindows_smul, pairClassProduct_smul]

omit [DecidableEq H] in
theorem rawIdeal_smul (e : Target counts) :
    letI rawInst : MulAction (HalfClassPermutations (ClassPositions counts))
        (RawPairs counts (Left leftLength) (Right rightLength)) :=
      EquivOrbitTransport.action (pairEquiv counts (Left leftLength) (Right rightLength) e)
    ∀ (g : HalfClassPermutations (ClassPositions counts))
      (x y z : RawPairs counts (Left leftLength) (Right rightLength)),
      JointCanonicalization.ideal counts (Left leftLength) (Right rightLength)
        (inputTensor (F := F) leftLength rightLength parentShape sharing)
        (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr e
        (@SMul.smul _ _ rawInst.toSMul g x)
        (@SMul.smul _ _ rawInst.toSMul g y)
        (@SMul.smul _ _ rawInst.toSMul g z) =
      JointCanonicalization.ideal counts (Left leftLength) (Right rightLength)
        (inputTensor leftLength rightLength parentShape sharing)
        (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr e x y z := by
  refine EquivOrbitTransport.coefficients_preserved
    (G := HalfClassPermutations (ClassPositions counts))
    (pairEquiv counts (Left leftLength) (Right rightLength) e)
    (pairEquiv counts (Left leftLength) (Right rightLength) e)
    (pairEquiv counts (Left leftLength) (Right rightLength) e)
    (JointCanonicalization.ideal counts (Left leftLength) (Right rightLength)
      (inputTensor (F := F) leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr e)
    (canonicalIdeal counts (Left leftLength) (Right rightLength)
      (inputTensor (F := F) leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr) ?_ ?_
  · exact ideal_eq_canonicalIdeal counts (Left leftLength) (Right rightLength)
      (inputTensor leftLength rightLength parentShape sharing)
      (coarse leftLength rightLength hleft) sl sr νl νr ηl ηr e
  · exact canonicalIdeal_smul counts leftLength rightLength parentShape sharing hleft
      sl sr νl νr ηl ηr hsupport

end MatrixMultiplication.JointCanonicalSymmetry

end
end

end MatrixAllFields

end OAI

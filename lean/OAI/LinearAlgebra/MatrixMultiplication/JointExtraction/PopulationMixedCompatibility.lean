import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.PopulationCompatibility
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.PopulationMixedNonzero
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWStrandCompatibility

namespace OAI

/-! Joint tensor extraction, compatibility and entropy estimates. -/

noncomputable section

namespace MatrixMultiplication.JointPopulationMixedCompatibility

open MatrixMultiplication.Foundation JointPopulation JointCanonicalization JointCanonicalCW
open JointPopulationCompatibility JointPopulationMixedNonzero CWStrands InheritedMasks
open CWStrandCompatibility
open scoped BigOperators

attribute [local instance] Classical.propDecidable

def sharingDesignated {H : Type*} (sharing : H → Bool)
    (d : JointPopulationCompatibility.ClassKey (H := H) → Shape → Prop)
    (c : JointPopulationCompatibility.ClassKey (H := H)) (u : Shape) : Prop :=
  sharing c.1 = true ∧ d c u

variable {H F : Type*} [Fintype H] [DecidableEq H] [Field F]
  (counts : H → Shape → ℕ) (leftLength rightLength : H → ℕ)
  (parentShape : H → Fin 3 → ℕ) (sharing : H → Bool) (hleft : ∀ h, leftLength h ≤ 8)
  (hsupport : ∀ h u, 0 < counts h u → sharing h = true → ∀ s, shapeNat u s ≤ parentShape h s)
  (e : Target counts)
  (x y z : RawPairs counts (Left leftLength) (Right rightLength))
  (hsource : sourceTensor counts (Left leftLength) (Right rightLength)
    (JointCanonicalMixed.inputTensor (F := F) leftLength rightLength parentShape sharing) x y z ≠ 0)
  (hx : coarseMask counts (Left leftLength) (Right rightLength)
    (coarse leftLength rightLength hleft) 0 e x)
  (hy : coarseMask counts (Left leftLength) (Right rightLength)
    (coarse leftLength rightLength hleft) 1 e y)
  (hz : coarseMask counts (Left leftLength) (Right rightLength)
    (coarse leftLength rightLength hleft) 2 e z)

variable (SL SR : H → Type*)
  [∀ h, Fintype (SL h)] [∀ h, DecidableEq (SL h)]
  [∀ h, Fintype (SR h)] [∀ h, DecidableEq (SR h)]
  (leftStatistic : ∀ h, Left leftLength h → SL h)
  (rightStatistic : ∀ h, Right rightLength h → SR h)
  (κLeft : ∀ h, SL h ≃ SL h) (κRight : ∀ h, SR h ≃ SR h)
  (hstatLeft : ∀ h w, leftStatistic h (CWCompatibilityTransfer.wordComplement w) =
    κLeft h (leftStatistic h w))
  (hstatRight : ∀ h w, rightStatistic h (CWCompatibilityTransfer.wordComplement w) =
    κRight h (rightStatistic h w))
  (xLeftLaw yLeftLaw : ∀ c : JointCanonicalization.ClassKey (H := H), SL c.1 → ℝ)
  (xRightLaw yRightLaw : ∀ c : JointCanonicalization.ClassKey (H := H), SR c.1 → ℝ)
  (χ : ℝ)

include hsource hx hy hz hsupport hstatLeft hstatRight

omit [DecidableEq H] in
theorem source_implies_compatibleY
    (leftLaw : ∀ c : JointPopulationCompatibility.ClassKey (H := H), Shape → SL c.1 → ℝ)
    (rightLaw : ∀ c : JointPopulationCompatibility.ClassKey (H := H), Shape → SR c.1 → ℝ)
    (hlaw : ∀ h u, 0 < counts h u → sharing h = true → designatedYLeft (h, shapeSide 1 u) u →
      leftLaw (h, shapeSide 1 u) u = xLeftLaw (h, u) ∘ (κLeft h).symm)
    (hrlaw : ∀ h u, 0 < counts h u → sharing h = true → designatedYRight parentShape (h, shapeSide 1 u) u →
      rightLaw (h, shapeSide 1 u) u = xRightLaw (h, u) ∘ (κRight h).symm)
    (huseX : ∀ h u, 0 < counts h u → sharing h = true →
      typeWindow (xLeftLaw (h, u)) χ
        (fun i : Class counts e h u => leftStatistic h (x h i.val).1) ∧
      typeWindow (xRightLaw (h, u)) χ
        (fun i : Class counts e h u => rightStatistic h (x h i.val).2)) :
    Compatible counts (Left leftLength) (Right rightLength)
      (fun c => SL c.1) (fun c => SR c.1)
      (fun c => leftStatistic c.1) (fun c => rightStatistic c.1)
      (sharingDesignated sharing designatedYLeft)
      (sharingDesignated sharing (designatedYRight parentShape)) leftLaw rightLaw χ 1 e y := by
  apply compatible_of_designated_windows
  · intro h u hn hd
    rw [hlaw h u hn hd.1 hd.2]
    exact zeroZ_transfer (fun _ : Class counts e h u => shapeNat u)
      (fun i => (x h i.val).1) (fun i => (y h i.val).1) (fun i => (z h i.val).1)
      (class_half_products_nonzero counts leftLength rightLength parentShape sharing hleft
        hsupport e x y z hsource hx hy hz h u hn hd.1).1
      (leftStatistic h) (κLeft h) (hstatLeft h) (xLeftLaw (h, u)) χ
      (fun _ => hd.2) (huseX h u hn hd.1).1
  · intro h u hn hd
    rw [hrlaw h u hn hd.1 hd.2]
    exact zeroZ_transfer (fun _ : Class counts e h u => parentShape h - shapeNat u)
      (fun i => (x h i.val).2) (fun i => (y h i.val).2) (fun i => (z h i.val).2)
      (class_half_products_nonzero counts leftLength rightLength parentShape sharing hleft
        hsupport e x y z hsource hx hy hz h u hn hd.1).2
      (rightStatistic h) (κRight h) (hstatRight h) (xRightLaw (h, u)) χ
      (fun _ => hd.2) (huseX h u hn hd.1).2

omit [DecidableEq H] in
theorem source_implies_compatibleZ
    (leftLaw : ∀ c : JointPopulationCompatibility.ClassKey (H := H), Shape → SL c.1 → ℝ)
    (rightLaw : ∀ c : JointPopulationCompatibility.ClassKey (H := H), Shape → SR c.1 → ℝ)
    (hlaw : ∀ h u, 0 < counts h u → sharing h = true → designatedZLeft (h, shapeSide 2 u) u →
      leftLaw (h, shapeSide 2 u) u =
        (if shapeNat u 1 = 0 then xLeftLaw (h, u) else yLeftLaw (h, u)) ∘
          (κLeft h).symm)
    (hrlaw : ∀ h u, 0 < counts h u → sharing h = true → designatedZRight parentShape (h, shapeSide 2 u) u →
      rightLaw (h, shapeSide 2 u) u =
        (if (parentShape h - shapeNat u) 1 = 0 then xRightLaw (h, u)
          else yRightLaw (h, u)) ∘ (κRight h).symm)
    (huseX : ∀ h u, 0 < counts h u → sharing h = true →
      typeWindow (xLeftLaw (h, u)) χ
        (fun i : Class counts e h u => leftStatistic h (x h i.val).1) ∧
      typeWindow (xRightLaw (h, u)) χ
        (fun i : Class counts e h u => rightStatistic h (x h i.val).2))
    (huseY : ∀ h u, 0 < counts h u → sharing h = true →
      typeWindow (yLeftLaw (h, u)) χ
        (fun i : Class counts e h u => leftStatistic h (y h i.val).1) ∧
      typeWindow (yRightLaw (h, u)) χ
        (fun i : Class counts e h u => rightStatistic h (y h i.val).2)) :
    Compatible counts (Left leftLength) (Right rightLength)
      (fun c => SL c.1) (fun c => SR c.1)
      (fun c => leftStatistic c.1) (fun c => rightStatistic c.1)
      (sharingDesignated sharing designatedZLeft)
      (sharingDesignated sharing (designatedZRight parentShape)) leftLaw rightLaw χ 2 e z := by
  apply compatible_of_designated_windows
  · intro h u hn hd
    rw [hlaw h u hn hd.1 hd.2]
    have hp := (class_half_products_nonzero counts leftLength rightLength parentShape sharing hleft
      hsupport e x y z hsource hx hy hz h u hn hd.1).1
    by_cases hzeroY : shapeNat u 1 = 0
    · rw [ite_eq_left hzeroY]
      exact zeroY_transfer (fun _ : Class counts e h u => shapeNat u)
        (fun i => (x h i.val).1) (fun i => (y h i.val).1) (fun i => (z h i.val).1) hp
        (leftStatistic h) (κLeft h) (hstatLeft h) (xLeftLaw (h, u)) χ
        (fun _ => hzeroY) (huseX h u hn hd.1).1
    · rw [ite_eq_right hzeroY]
      have hzeroX : shapeNat u 0 = 0 :=
        (Nat.mul_eq_zero.mp hd.2).resolve_right hzeroY
      exact zeroX_transfer (fun _ : Class counts e h u => shapeNat u)
        (fun i => (x h i.val).1) (fun i => (y h i.val).1) (fun i => (z h i.val).1) hp
        (leftStatistic h) (κLeft h) (hstatLeft h) (yLeftLaw (h, u)) χ
        (fun _ => hzeroX) (huseY h u hn hd.1).1
  · intro h u hn hd
    rw [hrlaw h u hn hd.1 hd.2]
    have hp := (class_half_products_nonzero counts leftLength rightLength parentShape sharing hleft
      hsupport e x y z hsource hx hy hz h u hn hd.1).2
    by_cases hzeroY : (parentShape h - shapeNat u) 1 = 0
    · rw [ite_eq_left hzeroY]
      exact zeroY_transfer (fun _ : Class counts e h u => parentShape h - shapeNat u)
        (fun i => (x h i.val).2) (fun i => (y h i.val).2) (fun i => (z h i.val).2) hp
        (rightStatistic h) (κRight h) (hstatRight h) (xRightLaw (h, u)) χ
        (fun _ => hzeroY) (huseX h u hn hd.1).2
    · rw [ite_eq_right hzeroY]
      have hzeroX : (parentShape h - shapeNat u) 0 = 0 :=
        (Nat.mul_eq_zero.mp hd.2).resolve_right hzeroY
      exact zeroX_transfer (fun _ : Class counts e h u => parentShape h - shapeNat u)
        (fun i => (x h i.val).2) (fun i => (y h i.val).2) (fun i => (z h i.val).2) hp
        (rightStatistic h) (κRight h) (hstatRight h) (yRightLaw (h, u)) χ
        (fun _ => hzeroX) (huseY h u hn hd.1).2

end MatrixMultiplication.JointPopulationMixedCompatibility

end

end OAI

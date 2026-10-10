import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootFlowGeneric

namespace OAI

/-!
# The reverse root flow used by a right-action shearing pair

For points separated on the right by g, sampling both at U(-t) gives
relative displacement U(t) g U(-t). This action has exactly the same
invariant sets as the original root flow, so its ergodicity follows
from full real-root ergodicity, without selecting a discrete time.
-/

noncomputable section
open MeasureTheory Filter Set

namespace DukePrimeDegree
open PrimeDegreePackets

@[instance_reducible] def reverseRootTranslationAction {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) : MulAction (Multiplicative ℝ) (X n) where
  smul t x := rightAction x (Matrix.SpecialLinearGroup.transvection hij (-t.toAdd))
  one_smul x := by
    change rightAction x (Matrix.SpecialLinearGroup.transvection hij (-0)) = x
    simp
  mul_smul t u x := by
    change rightAction x (Matrix.SpecialLinearGroup.transvection hij (-(t.toAdd + u.toAdd))) =
      rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij (-u.toAdd)))
        (Matrix.SpecialLinearGroup.transvection hij (-t.toAdd))
    rw [rightAction_mul, ← Matrix.SpecialLinearGroup.transvection_add]
    congr 2
    ring

lemma reverseRootTranslationAction_continuous {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) :
    let := reverseRootTranslationAction hij
    ContinuousSMul (Multiplicative ℝ) (X n) := by
  let := reverseRootTranslationAction hij
  constructor
  have hu : Continuous (fun t : Multiplicative ℝ =>
      Matrix.SpecialLinearGroup.transvection hij (-t.toAdd)) :=
    (continuous_rootTransvection hij).comp (by fun_prop)
  exact (continuous_rightAction_uncurry n).comp
    (continuous_snd.prodMk (hu.comp continuous_fst))

theorem reverseRootTranslationAction_ergodic {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (μ : Measure (X n))
    (herg : let := rootTranslationAction hij
      ErgodicSMul (Multiplicative ℝ) (X n) μ) :
    let := reverseRootTranslationAction hij
    ErgodicSMul (Multiplicative ℝ) (X n) μ := by
  let := reverseRootTranslationAction hij
  refine { measure_preimage_smul := ?_, aeconst_of_forall_preimage_smul_ae_eq := ?_ }
  · intro t B hB
    change μ ((fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij (-t.toAdd))) ⁻¹' B) = μ B
    let := rootTranslationAction hij
    let : ErgodicSMul (Multiplicative ℝ) (X n) μ := herg
    exact SMulInvariantMeasure.measure_preimage_smul
      (Multiplicative.ofAdd (-t.toAdd)) hB
  · intro B hB hfix
    have hf (t : Multiplicative ℝ) :
        (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij t.toAdd)) ⁻¹' B =ᵐ[μ] B := by
      have ht := hfix (Multiplicative.ofAdd (-t.toAdd))
      change (fun x => rightAction x
        (Matrix.SpecialLinearGroup.transvection hij (-(-t.toAdd)))) ⁻¹' B =ᵐ[μ] B at ht
      simpa only [neg_neg] using ht
    let := rootTranslationAction hij
    let : ErgodicSMul (Multiplicative ℝ) (X n) μ := herg
    exact ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq hB hf

lemma reverse_root_pair_displacement {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) (x : X n) (g : G n) (t : ℝ) :
    rightAction (rightAction x g) (Matrix.SpecialLinearGroup.transvection hij (-t)) =
      rightAction (rightAction x (Matrix.SpecialLinearGroup.transvection hij (-t)))
        (Matrix.SpecialLinearGroup.transvection hij t * g *
          Matrix.SpecialLinearGroup.transvection hij (-t)) := by
  simp only [rightAction_mul]
  congr 1
  rw [← Matrix.SpecialLinearGroup.transvection_inv hij t]
  group

end DukePrimeDegree

end

end OAI

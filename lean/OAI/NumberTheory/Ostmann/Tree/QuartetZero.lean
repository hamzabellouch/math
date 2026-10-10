import OAI.NumberTheory.Ostmann.Tree.AffinePairIdentity
import OAI.NumberTheory.Ostmann.Tree.QuartetDiagram

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
variable {F : Type*} [Field F]

namespace NodeInput
variable {d : ℕ}

theorem ratio_eq_one_of_pivot_zero (N : NodeInput F d) (hp : N.pivot=0) :
    ratio N.left.frequency N.right.frequency N.leftFactor N.rightFactor = 1 := by
  have hd : (N.s:F)*N.u ≠ 0 := mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  have he := congrArg (fun x : F => x*((N.s:F)*N.u)) hp
  change (((N.left.frequency:F)*N.rightFactor-(N.right.frequency:F)*N.leftFactor)/
    ((N.s:F)*N.u))*((N.s:F)*N.u) = 0*((N.s:F)*N.u) at he
  rw [div_mul_cancel₀ _ hd, zero_mul] at he
  have hn : (N.left.frequency:F)*N.rightFactor=(N.right.frequency:F)*N.leftFactor := sub_eq_zero.mp he
  apply Units.ext
  simp only [ratio, Units.val_div_eq_div_val, Units.val_mul, Units.val_one]
  exact (div_eq_one_iff_eq (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))).mpr hn

def factorRatio (N : NodeInput F d) (freeRight : Bool) : Fˣ :=
  if freeRight then ratio N.right.frequency N.left.frequency N.rightFactor N.leftFactor
  else ratio N.left.frequency N.right.frequency N.leftFactor N.rightFactor

theorem reversed_ratio (sf sh Hf Hh : Fˣ) :
    ratio sh sf Hh Hf = (ratio sf sh Hf Hh)⁻¹ := by
  simp [ratio, div_eq_mul_inv, mul_comm]

theorem factorRatio_zero (N : NodeInput F d) (hp : N.pivot=0) (freeRight : Bool) :
    N.factorRatio freeRight = 1 := by
  cases freeRight
  · exact ratio_eq_one_of_pivot_zero N hp
  · change ratio N.right.frequency N.left.frequency N.rightFactor N.leftFactor = 1
    rw [reversed_ratio, ratio_eq_one_of_pivot_zero N hp, inv_one]

theorem orientedRatio_eq_factorRatio (N : NodeInput F 0) (hp : N.pivot ≠ 0)
    (freeRight : Bool) : N.orientedRatio hp freeRight = N.factorRatio freeRight := by
  cases freeRight
  · exact actual_child_ratio N hp
  · change N.rightArgument hp/N.leftArgument hp =
      ratio N.right.frequency N.left.frequency N.rightFactor N.leftFactor
    rw [leftArgument_eq, rightArgument_eq, child_ratio]

theorem signedFunction_zero (g : F → ℂ) (hg0 : g 0=0) (sign : Bool) :
    signedFunction g sign 0=0 := by
  cases sign <;> simp [signedFunction, hg0]

theorem bottom_evaluate_all (N : NodeInput F 0) (hopp : N.parameters.bottomOpposite)
    (g : F → ℂ) (hg0 : g 0=0) (incoming : F) (freeRight : Bool) :
    N.parameters.evaluate g N.D N.Xleft N.Xright incoming N.leaves =
      pairValue g (N.orientedSign freeRight) (orientation freeRight) (N.argument:F)
        (N.factorRatio freeRight:F) := by
  classical
  by_cases hp : N.pivot=0
  · rw [evaluate_eq_zero N hp g incoming, factorRatio_zero N hp freeRight]
    simp [pairValue, Ostmann.FiniteField.pairFirst, Ostmann.FiniteField.pairSecond,
      signedFunction_zero g hg0]
  · rw [bottom_evaluate_oriented N hp hopp g incoming freeRight,
      orientedRatio_eq_factorRatio]

end NodeInput

theorem pairValue_eq_pairTest {p : ℕ} [Fact p.Prime] (g : ZMod p → ℂ) (sign : Bool)
    (σ : (ZMod p)ˣ) (d t : ZMod p) :
    pairValue g sign σ d t = Ostmann.FiniteField.pairTest (signedFunction g sign) σ d t := rfl

end
end Ostmann.Tree.Quartet

end OAI

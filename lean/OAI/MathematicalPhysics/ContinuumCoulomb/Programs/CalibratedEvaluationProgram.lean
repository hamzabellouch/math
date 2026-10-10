import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedEvaluationComponents

namespace OAI

/-! The final polynomial TM2 composition for the actual calibrated residual. -/

namespace ContinuumCoulomb.CalibratedEvaluation
open ExactQuantumFactoring.BitStackProgram

attribute [local irreducible] CoulombEvaluation.approximate

noncomputable def evaluatedExpression (rho : ℕ) (x : Environment × ℚ) : ℚ :=
  (x.1.2.1 : ℚ) *
    ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2) -
      x.1.2.2.1 * root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2

theorem evaluatedExpression_eq (rho : ℕ) (x : Environment × ℚ) :
    evaluatedExpression rho x = value rho x.1 x.2 := rfl

noncomputable opaque valuesProgram (rho : ℕ) : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => ((x.1.2.1 : ℚ) *
      ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2),
        x.1.2.2.1 * root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2)) :=
  scaledHoppingProgram.pair (targetProgram rho)

noncomputable opaque subtractValuesProgram (rho : ℕ) : Procedure inputCode ratCode
    ((fun q : ℚ × ℚ => q.1 - q.2) ∘ (fun x : Environment × ℚ => ((x.1.2.1 : ℚ) *
      ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2),
        x.1.2.2.1 * root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2))) :=
  Procedure.ratSub.comp (valuesProgram rho)

private theorem subtract_pair_function {X : Type*} (f g : X → ℚ) :
    ((fun q : ℚ × ℚ => q.1 - q.2) ∘ (fun x => (f x, g x))) =
      (fun x => f x - g x) := rfl

theorem subtractValues_function (rho : ℕ) :
    ((fun q : ℚ × ℚ => q.1 - q.2) ∘ (fun x : Environment × ℚ => ((x.1.2.1 : ℚ) *
      ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2),
        x.1.2.2.1 * root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2))) = evaluatedExpression rho := by
  exact subtract_pair_function _ _

noncomputable opaque rawProgram (rho : ℕ) : Procedure inputCode ratCode (evaluatedExpression rho) :=
  cast (congrArg (fun f : Environment × ℚ → ℚ => Procedure inputCode ratCode f)
    (subtractValues_function rho)) (subtractValuesProgram rho)

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode
    (fun x => value rho x.1 x.2) :=
  cast (congrArg (fun f : Environment × ℚ → ℚ => Procedure inputCode ratCode f)
    (funext (evaluatedExpression_eq rho))) (rawProgram rho)

noncomputable def certificate (rho : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode ratCode (fun x => value rho x.1 x.2) :=
  (program rho).toTM2

end ContinuumCoulomb.CalibratedEvaluation

end OAI

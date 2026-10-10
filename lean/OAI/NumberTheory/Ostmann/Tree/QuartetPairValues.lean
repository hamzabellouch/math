import OAI.NumberTheory.Ostmann.Tree.QuartetCoordinates

namespace OAI

namespace Ostmann.Tree.Quartet
noncomputable section
open scoped ComplexConjugate
variable {F : Type*} [Field F]

theorem pair_coordinates_of_difference (σ d x z : Fˣ)
    (hd : (x:F)-(z:F)=(σ:F)*d) :
    Ostmann.FiniteField.pairFirst σ (d:F) ((x/z:Fˣ):F) = (x:F) ∧
      Ostmann.FiniteField.pairSecond σ (d:F) ((x/z:Fˣ):F) = (z:F) := by
  have hdiff : (x:F)-(z:F) ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (Units.ne_zero σ) (Units.ne_zero d)
  have hratio : (x:F)/(z:F)-1 = ((x:F)-(z:F))/(z:F) := by
    field_simp
  constructor
  · simp only [Ostmann.FiniteField.pairFirst, Units.val_div_eq_div_val]
    rw [← hd, hratio]
    field_simp
  · simp only [Ostmann.FiniteField.pairSecond, Units.val_div_eq_div_val]
    rw [← hd, hratio]
    field_simp

def signedFunction (g : F → ℂ) (sign : Bool) : F → ℂ :=
  if sign then fun x => conj (g x) else g

def pairValue (g : F → ℂ) (sign : Bool) (σ : Fˣ) (d t : F) : ℂ :=
  signedFunction g sign (Ostmann.FiniteField.pairFirst σ d t) *
    conj (signedFunction g sign (Ostmann.FiniteField.pairSecond σ d t))

namespace NodeInput
variable {d : ℕ}

theorem pair_coordinates_left (N : NodeInput F d) (hp : N.pivot ≠ 0) :
    Ostmann.FiniteField.pairFirst (1:Fˣ) (N.argument:F)
      ((N.leftArgument hp/N.rightArgument hp:Fˣ):F) = (N.leftArgument hp:F) ∧
    Ostmann.FiniteField.pairSecond (1:Fˣ) (N.argument:F)
      ((N.leftArgument hp/N.rightArgument hp:Fˣ):F) = (N.rightArgument hp:F) := by
  apply pair_coordinates_of_difference
  simpa only [Units.val_one, one_mul] using argument_difference N hp

theorem pair_coordinates_right (N : NodeInput F d) (hp : N.pivot ≠ 0) :
    Ostmann.FiniteField.pairFirst (-1:Fˣ) (N.argument:F)
      ((N.rightArgument hp/N.leftArgument hp:Fˣ):F) = (N.rightArgument hp:F) ∧
    Ostmann.FiniteField.pairSecond (-1:Fˣ) (N.argument:F)
      ((N.rightArgument hp/N.leftArgument hp:Fˣ):F) = (N.leftArgument hp:F) := by
  apply pair_coordinates_of_difference
  have h := argument_difference N hp
  simpa only [Units.val_neg, Units.val_one, neg_one_mul, neg_sub] using congrArg Neg.neg h

def leafSign (P : Parameters F 0) : Bool :=
  match P with | .leaf _ c => c

theorem bottom_evaluate_left (N : NodeInput F 0) (hp : N.pivot ≠ 0)
    (hopp : N.parameters.bottomOpposite) (g : F → ℂ) (incoming : F) :
    N.parameters.evaluate g N.D N.Xleft N.Xright incoming N.leaves =
      pairValue g (leafSign N.left) 1 (N.argument:F)
        ((N.leftArgument hp/N.rightArgument hp:Fˣ):F) := by
  rw [evaluate_eq N hp g incoming]
  unfold pairValue
  rw [(pair_coordinates_left N hp).1, (pair_coordinates_left N hp).2]
  cases hl : N.left with
  | leaf sl cl =>
    cases hr : N.right with
    | leaf sr cr =>
      simp only [parameters, hl, hr, Parameters.bottomOpposite] at hopp
      simp only [Parameters.evaluate, leafSign]
      cases cl <;> cases cr <;> simp_all [signedFunction]

theorem bottom_evaluate_right (N : NodeInput F 0) (hp : N.pivot ≠ 0)
    (hopp : N.parameters.bottomOpposite) (g : F → ℂ) (incoming : F) :
    N.parameters.evaluate g N.D N.Xleft N.Xright incoming N.leaves =
      pairValue g (leafSign N.right) (-1) (N.argument:F)
        ((N.rightArgument hp/N.leftArgument hp:Fˣ):F) := by
  rw [evaluate_eq N hp g incoming]
  unfold pairValue
  rw [(pair_coordinates_right N hp).1, (pair_coordinates_right N hp).2]
  cases hl : N.left with
  | leaf sl cl =>
    cases hr : N.right with
    | leaf sr cr =>
      simp only [parameters, hl, hr, Parameters.bottomOpposite] at hopp
      simp only [Parameters.evaluate, leafSign]
      cases cl <;> cases cr <;> simp_all [signedFunction, mul_comm]

end NodeInput
end
end Ostmann.Tree.Quartet

end OAI

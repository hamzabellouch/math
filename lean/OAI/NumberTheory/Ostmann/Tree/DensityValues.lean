import OAI.NumberTheory.Ostmann.Tree.DensityAlgebra

namespace OAI

namespace Ostmann.Tree.Density
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F : Type*} [Field F]

def weight {d : ℕ} (g : F → ℂ) (y : Leaves d → Fˣ) : ℝ := ∏ v, ‖g (y v)‖^2

def mass {d : ℕ} (g : F → ℂ) (y : Option (Leaves d → Fˣ)) : ℝ :=
  match y with | none => 0 | some z => weight g z

theorem weight_join {d : ℕ} (g : F → ℂ) (yl yr : Leaves d → Fˣ) :
    weight g (join yl yr) = weight g yl * weight g yr := by
  unfold weight
  rw [prod_split]
  simp only [left, right, join, Fin.cons_zero, Bool.false_eq_true, ↓reduceIte, Fin.tail_cons]

theorem mass_join {d : ℕ} (g : F → ℂ) (yl yr : Option (Leaves d → Fˣ)) :
    mass g (match yl, yr with | some l, some r => some (join l r) | _, _ => none) =
      mass g yl * mass g yr := by
  cases yl <;> cases yr <;> simp [mass, weight_join]

theorem evaluate_norm_sq {d : ℕ} (P : Parameters F d) (g : F → ℂ)
    (D Xl Xr c : Fˣ) (M : Leaves d → Fˣ) :
    ‖P.evaluate g D Xl Xr (rootArgument P D Xl Xr c M : F) M‖^2 =
      mass g (reconstruct D P Xl Xr c M) := by
  classical
  induction P generalizing D Xl Xr c with
  | leaf s sign =>
    cases sign <;> simp [Parameters.evaluate, reconstruct, mass, weight]
  | @branch d s a b u L R ihl ihr =>
    change ‖(if hp : pivot s a b u L R Xl Xr M = 0 then 0 else
      L.evaluate g D (Units.mk0 _ hp) Xl
        ((L.frequency : F) / ((D : F)*(Units.mk0 _ hp : Fˣ)*u*
          (Xl*a*Parameters.leafProduct (left M)))) (left M) *
      R.evaluate g D (Units.mk0 _ hp) Xr
        ((R.frequency : F) / ((D : F)*(Units.mk0 _ hp : Fˣ)*u*
          (Xr*b*Parameters.leafProduct (right M)))) (right M))‖^2 = _
    by_cases hp : pivot s a b u L R Xl Xr M = 0
    · simp [hp, reconstruct, mass]
    · simp only [dite_eq_right hp, norm_mul, mul_pow, reconstruct]
      rw [← child_rootArgument, ← child_rootArgument]
      rw [ihl, ihr]
      exact (mass_join g
        (reconstruct D L (Units.mk0 _ hp) Xl (u*a) (left M))
        (reconstruct D R (Units.mk0 _ hp) Xr (u*b) (right M))).symm

def rootCoefficient : {d : ℕ} → Parameters F d → Fˣ
  | _, .leaf _ _ => 1
  | _, .branch _ a b _ _ _ => a*b

theorem rootCoefficient_consistent {d : ℕ} (P : Parameters F d) :
    P.childConsistent (rootCoefficient P) := by cases P <;> simp [Parameters.childConsistent, rootCoefficient]

def diagramArguments {d : ℕ} (T : Diagram F d) (M : Leaves d → Fˣ) :
    Option (Leaves d → Fˣ) :=
  match d, T with
  | 0, T => reconstruct 1 T.parameters 1 1 1 M
  | _+1, T => reconstruct T.denominator T.parameters T.rootLeft T.rootRight
    (rootCoefficient T.parameters) M

theorem diagram_value_norm_sq {d : ℕ} (T : Diagram F d) (g : F → ℂ)
    (M : Leaves d → Fˣ) :
    ‖T.value g M‖^2 = mass g (diagramArguments T M) := by
  cases d with
  | zero =>
    cases hp : T.parameters with
    | leaf s sign =>
      cases sign <;> simp [Diagram.value, Parameters.value, diagramArguments, hp,
        reconstruct, rootArgument, Parameters.frequency, Parameters.leafProduct,
        mass, weight]
      all_goals exact congrArg (fun v : Leaves 0 => ‖g ((s:F) / (M v:F))‖) (Subsingleton.elim _ _)
  | succ d =>
    cases hp : T.parameters with
    | branch s a b u L R =>
      have he := evaluate_norm_sq (.branch s a b u L R) g
        T.denominator T.rootLeft T.rootRight (a*b) M
      simpa only [Diagram.value, Parameters.value, diagramArguments, hp,
        rootCoefficient, Parameters.evaluate] using he

end
end Ostmann.Tree.Density

end OAI

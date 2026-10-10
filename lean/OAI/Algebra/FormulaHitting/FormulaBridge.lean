import OAI.Algebra.FormulaHitting.Specification
import OAI.Algebra.FormulaHitting.Formula

namespace OAI

namespace NCHittingSpecification

namespace Formula

def toImplementation {F : Type*} {n : ℕ} : Formula F n → NCHitting.Formula F n
  | .scalar a => .scalar a
  | .variable i => .var i
  | .add f g => .add (toImplementation f) (toImplementation g)
  | .multiply f g => .mul (toImplementation f) (toImplementation g)

@[simp] theorem toImplementation_size {F : Type*} {n : ℕ} (f : Formula F n) :
    f.toImplementation.size = f.gates := by
  induction f <;> simp_all [toImplementation, gates, NCHitting.Formula.size]

@[simp] theorem toImplementation_coeff {F : Type*} {n : ℕ} [Semiring F]
    (f : Formula F n) (w : List (Fin n)) :
    f.toImplementation.coeff w = f.coefficient w := by
  induction f generalizing w with
  | scalar a => rfl
  | «variable» i => rfl
  | add f g hf hg => simp [toImplementation, NCHitting.Formula.coeff, coefficient, hf, hg]
  | multiply f g hf hg =>
    simp [toImplementation, NCHitting.Formula.coeff, coefficient,
      NCHitting.convolution_eq_sum, hf, hg]

@[simp] theorem toImplementation_eval {F : Type*} {n d : ℕ} [Field F]
    (f : Formula F n) (T : Fin n → Matrix (Fin d) (Fin d) F) :
    f.toImplementation.eval (Matrix.scalar (Fin d)) T = f.evaluate T := by
  induction f <;> simp_all [toImplementation, NCHitting.Formula.eval, evaluate]

end Formula

end NCHittingSpecification

end OAI

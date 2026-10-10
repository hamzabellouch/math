import OAI.Combinatorics.PolynomialVacuum.Algebra.BaseThree
import OAI.Combinatorics.PolynomialVacuum.Algebra.InterpolatedCups
import OAI.Combinatorics.PolynomialVacuum.Algebra.InterpolatedZero
import OAI.Combinatorics.PolynomialVacuum.Algebra.InterpolatedDegrees

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def basePolyTwo {ι : Type*} (x y : MvPolynomial ι ℂ) : Spin → Spin → MvPolynomial ι ℂ
  | .zero,.zero => x+y
  | .plus,.minus => C (q^5-q^7)*y
  | .minus,.plus => C (q-q^3)*x
  | _,_ => 0

noncomputable def basePolyThreeFactor {ι : Type*} (x y z : MvPolynomial ι ℂ) : MvPolynomial ι ℂ :=
  (z+C (q^2)*x)*(z-C (q^6)*y)

noncomputable def basePolyThree {ι : Type*} (x y z : MvPolynomial ι ℂ) : Spin → Spin → Spin → MvPolynomial ι ℂ
  | .zero,.zero,.zero => x^2*y+x^2*z+y^2*x+y^2*z+z^2*x+z^2*y+C (2*(q^2-q^6))*x*y*z
  | .plus,.minus,.zero => C (q^5-q^7)*y*basePolyThreeFactor x y z
  | .minus,.plus,.zero => C (q-q^3)*x*basePolyThreeFactor x y z
  | .zero,.plus,.minus => C (q^5-q^7)*z*basePolyThreeFactor y z x
  | .zero,.minus,.plus => C (q-q^3)*y*basePolyThreeFactor y z x
  | .plus,.zero,.minus => C (q^5-q^7)*z*basePolyThreeFactor z x y
  | .minus,.zero,.plus => C (q-q^3)*x*basePolyThreeFactor z x y
  | _,_,_ => 0

noncomputable def vacuumZero : State 0 := fun _ => 1
noncomputable def vacuumOne : State 1 := fun s => if s 0=Spin.zero then 1 else 0
noncomputable def vacuumTwo : State 2 := fun s => basePolyTwo (X 0) (X 1) (s 0) (s 1)
noncomputable def vacuumThree : State 3 := fun s => basePolyThree (X 0) (X 1) (X 2) (s 0) (s 1) (s 2)

@[simp] theorem eval_basePolyTwo {ι : Type*} (x y : MvPolynomial ι ℂ) (a b : Spin) (Y : ι → ℂ) :
    eval Y (basePolyTwo x y a b)=baseTwo (eval Y x) (eval Y y) a b := by
  cases a <;> cases b <;> simp [basePolyTwo,baseTwo]

@[simp] theorem eval_basePolyThree {ι : Type*} (x y z : MvPolynomial ι ℂ) (a b c : Spin) (Y : ι → ℂ) :
    eval Y (basePolyThree x y z a b c)=baseThree (eval Y x) (eval Y y) (eval Y z) a b c := by
  cases a <;> cases b <;> cases c <;> simp [basePolyThree,basePolyThreeFactor,baseThree,baseThreeFactor]

@[simp] theorem lift_vacuumZero (Y : ℕ → ℂ) (s : ℕ → Spin) : liftState vacuumZero Y s=1 := by simp [liftState,liftPolyTensor,vacuumZero]
@[simp] theorem lift_vacuumOne (Y : ℕ → ℂ) (s : ℕ → Spin) : liftState vacuumOne Y s=(if s 0=Spin.zero then 1 else 0) := by simp [liftState,liftPolyTensor,vacuumOne]
@[simp] theorem lift_vacuumTwo (Y : ℕ → ℂ) (s : ℕ → Spin) : liftState vacuumTwo Y s=baseTwo (Y 0) (Y 1) (s 0) (s 1) := by simp [liftState,liftPolyTensor,vacuumTwo]
@[simp] theorem lift_vacuumThree (Y : ℕ → ℂ) (s : ℕ → Spin) : liftState vacuumThree Y s=baseThree (Y 0) (Y 1) (Y 2) (s 0) (s 1) (s 2) := by simp [liftState,liftPolyTensor,vacuumThree]

end PolynomialVacuumAlgebra

end OAI

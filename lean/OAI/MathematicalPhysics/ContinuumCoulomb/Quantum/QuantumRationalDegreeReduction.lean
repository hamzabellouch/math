import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRationalFork
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDegreeReduction

namespace OAI

/-! The full degree-three reduction has exact rational output coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaRationalSubdivision {n m : ℕ} (left right : Fin m → Fin n)
    (J : Fin m → ℚ) (constant R : ℚ) : QMARationalForkNetwork n where
  graph := qmaSubdivisionNetwork left right
  weight := fun _ => R^2
  active := fun p => ![R,2*R*J (qmaOriginalPortEquiv left right p).1]
    (qmaOriginalPortEquiv left right p).2
  constant := (constant+∑ e, (3/4+3*(J e)^2))+3*(m:ℚ)*R^2

theorem qmaRationalSubdivision_real {n m : ℕ} (left right : Fin m → Fin n)
    (J : Fin m → ℚ) (constant R : ℚ) :
    (qmaRationalSubdivision left right J constant R).real =
      qmaSubdivisionWeighted left right (fun e => (J e:ℝ)) constant R := by
  unfold qmaRationalSubdivision QMARationalForkNetwork.real qmaSubdivisionWeighted
  congr 1
  · funext e
    push_cast
    rfl
  · funext p
    generalize h : (qmaOriginalPortEquiv left right p).2 = b
    fin_cases b <;> simp_all [qmaPathAmplitude]
  · simp [qmaPathOffset]

def qmaRationalInitialScale {m : ℕ} (J : Fin m → ℚ) (constant N : ℚ) : ℚ :=
  let A := 3*∑ e, (1+2*|J e|)
  let B := |constant|+4*∑ e, (1+|J e|)^2
  16*(A+B+1)^3*N+4*(A+B+1)+1

theorem qmaRationalInitialScale_cast {m : ℕ} (J : Fin m → ℚ) (constant N : ℚ) :
    (qmaRationalInitialScale J constant N:ℝ) =
      qmaRoutingScale (3*∑ e, (1+2*|(J e:ℝ)|))
        (|(constant:ℝ)|+4*∑ e, (1+|(J e:ℝ)|)^2) N := by
  simp [qmaRationalInitialScale,qmaRoutingScale]

def qmaRationalDegreeReduction {n m : ℕ} (left right : Fin m → Fin n)
    (J : Fin m → ℚ) (constant N : ℚ) (D : ℕ) : QMARationalForkNetwork n :=
  (qmaRationalSubdivision left right J constant (qmaRationalInitialScale J constant N)).iterate N D

theorem qmaRationalDegreeReduction_real {n m : ℕ} (left right : Fin m → Fin n)
    (J : Fin m → ℚ) (constant N : ℚ) (D : ℕ) :
    (qmaRationalDegreeReduction left right J constant N D).real =
      qmaDegreeReduction left right (fun e => (J e:ℝ)) constant N D := by
  unfold qmaRationalDegreeReduction qmaDegreeReduction
  rw [QMARationalForkNetwork.iterate_real,qmaRationalSubdivision_real,qmaRationalInitialScale_cast]

end ContinuumCoulomb

end

end OAI

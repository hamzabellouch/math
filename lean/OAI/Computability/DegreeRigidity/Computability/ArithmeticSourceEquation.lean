import OAI.Computability.DegreeRigidity.Computability.ArithmeticProgramGraph
import OAI.Computability.DegreeRigidity.Computability.ArithmeticShuffleGraph
import OAI.Computability.DegreeRigidity.Computability.ArithmeticPrincipalIntersection

namespace OAI


namespace TuringRigidity.ArithmeticSourceEquation
open UniformArithmetic ArithmeticProgramGraph ArithmeticShuffleGraph GenericIdentity

theorem equation_arith (p : OracleCode) {P Y L R : OracleFamily}
    (hP : ArithmeticOracle P) (hY : ArithmeticOracle Y)
    (hL : ArithmeticOracle L) (hR : ArithmeticOracle R) :
    Arith (fun O v => SourceEquation p (P O v) (Y O v, L O v, R O v)) := by
  have hYL := code_arith hY hL
  have hYR := code_arith hY hR
  have hi := ArithmeticPrincipalIntersection.principal_arith (value_arith p hP hY)
    (join_arith (value_arith p hP hYL) (value_arith p hP hL))
    (join_arith (value_arith p hP hYR) (value_arith p hP hR))
  exact (total_arith p hP hY).and ((total_arith p hP hL).and
    ((total_arith p hP hR).and ((total_arith p hP hYL).and
      ((total_arith p hP hYR).and hi))))

theorem sourceEquation_arith (p : OracleCode) :
    Arith (fun O _ => SourceEquation p (O 0) (O 1, O 2, O 3)) :=
  equation_arith p (parameter_arith 0) (parameter_arith 1)
    (parameter_arith 2) (parameter_arith 3)

end TuringRigidity.ArithmeticSourceEquation

end OAI

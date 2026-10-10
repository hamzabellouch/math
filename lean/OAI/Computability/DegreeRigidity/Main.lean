import OAI.Computability.DegreeRigidity.Representation.GlobalArithmeticGenericProgram
import OAI.Computability.DegreeRigidity.CohenForcing.InternalCohenRequirements

namespace OAI


namespace TuringRigidity.ManuscriptMain
open TransitiveNameModel BoundedSetTheory CountableForcing GenericIdentity OracleJump

theorem generic_program_representation (π : Degree ≃o Degree) : GenericProgramRepresentation π := by
  obtain ⟨R,p,_,hrep⟩ := RelativeConstructible.global_arithmetic_generic_program π
  obtain ⟨M,hM,hT,hcount,_,_,hRM,_,_⟩ :=
    PrescribedFirstUncountable.prescribed_covering_model_with_omega_one π (fun _ => R)
  let := hcount
  have hP := sourceT_real_iterate M hM hT (hRM 0) 5
  obtain ⟨D,hD,hground⟩ := InternalCohen.ground_family M ⟨realCode.{0} R,hRM 0⟩
  refine ⟨D,hD,iterate R 5,p,?_⟩
  intro A hA
  have ha := GroundArithmeticGeneric.ground_arithmetic M hM hT (fun _ => iterate R 5)
    (fun _ => hP) A ((hground A).mp hA)
  obtain ⟨ht,hπ⟩ := hrep A ha
  exact ⟨value p (iterate R 5) A,(total_iff p (iterate R 5) A).mp ht,hπ⟩

theorem borel_representation : BorelRepresentation :=
  fun π => borel_of_generic_program π (generic_program_representation π)

theorem rigidity : MainTheorem := main_of_representation borel_representation

end TuringRigidity.ManuscriptMain

end OAI

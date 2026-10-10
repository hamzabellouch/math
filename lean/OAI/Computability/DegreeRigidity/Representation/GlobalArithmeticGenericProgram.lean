import OAI.Computability.DegreeRigidity.Representation.PrescribedArithmeticGenericProgram
import OAI.Computability.DegreeRigidity.Representation.PrescribedFirstUncountable
import OAI.Computability.DegreeRigidity.CohenForcing.CohenGroundGeneric

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing ElementaryModel PersistentRestrictions
open GenericIdentity OracleJump CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem global_arithmetic_generic_program (π : Degree ≃o Degree) :
    ∃ (R : Oracle) (p : OracleCode),
      degree R = π.symm (degree (jump FixedArithmetic.zero)) ∧
      ∀ Y : Oracle, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) Y →
        RepresentsAt π p (iterate R 5) Y := by
  classical
  by_contra hnone
  push Not at hnone
  let d := π.symm (degree (jump FixedArithmetic.zero))
  let C := {R : Oracle // degree R = d} × OracleCode
  let : Countable {R : Oracle // degree R = d} := (countable_degree_fiber d).to_subtype
  obtain ⟨R₀,hR₀⟩ := degree_surjective d
  let : Nonempty C := ⟨(⟨R₀,hR₀⟩,OracleCode.zero)⟩
  have hw : ∀ c : C, ∃ Y : Oracle,
      ArithmeticPrefixForcing.Generic (fun _ => iterate c.1.val 5) Y ∧
      ¬ RepresentsAt π c.2 (iterate c.1.val 5) Y := by
    intro c
    exact hnone c.1.val c.2 c.1.property
  choose W hWg hWbad using hw
  obtain ⟨e,he⟩ := exists_surjective_nat C
  obtain ⟨M,hM,hT,hcount,_,⟨K,hK⟩,hWM,himages,ρ,hρ,_,_,_⟩ :=
    PrescribedFirstUncountable.prescribed_covering_model_with_omega_one π (fun n => W (e n))
  let := hcount
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hK.2.1 (sourceT_omega_mem M hM hT)
  obtain ⟨G,_,hG,hME,_,_,_⟩ := CohenGroundGeneric.exists_extension M (ZFSet.prod K ZFSet.omega)
    hM hT hA ⊤
  obtain ⟨R,p,_,hR,_,_,hrep,_⟩ :=
    prescribed_arithmetic_generic_program π M K hM hT hK himages ρ hρ G hG
  let c : C := (⟨R,hR⟩,p)
  obtain ⟨n,hn⟩ := he c
  have hW : W c ∈ modelReals M := by simpa only [hn] using hWM n
  exact hWbad c (hrep (W c) (hME hW) (hWg c))

end TuringRigidity.RelativeConstructible

end OAI

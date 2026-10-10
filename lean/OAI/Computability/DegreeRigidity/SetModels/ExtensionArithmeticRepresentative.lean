import OAI.Computability.DegreeRigidity.Constructibility.PersistentLocality
import OAI.Computability.DegreeRigidity.Computability.JumpProperties

namespace OAI

namespace TuringRigidity.ExtensionArithmeticRepresentative
open OracleJump IdealInterpretation IdealLocality PersistentRestrictions PersistentLocality

theorem literal_join_program {I : DegreeIdeal} (σ : I ≃o I) (z x : I)
    (hz : z.val = degree (jump FixedArithmetic.zero)) (A R : Oracle)
    (hA : degree A = x.val) (hR : degree R = (σ.symm z).val) :
    ∃ X : Oracle, degree X = (σ x).val ∧ Reduces X (iterate (join A R) 5) ∧
      ∃ e : OracleCode,
        OracleCode.eval (oracleFunction (iterate (join A R) 5)) e = oracleFunction X := by
  obtain ⟨X,Y,hX,hY,hXY⟩ := image_arithmetic σ z hz x
  have hjoin : degree Y = degree (join A R) := by
    change degree Y = degree A ⊔ degree R
    rw [hA,hR]; exact hY
  have hred : Reduces X (iterate (join A R) 5) :=
    TuringReducible.trans hXY (iterate_mono ((degree_eq_iff _ _).mp hjoin).1 5)
  exact ⟨X,hX,hred,OracleCode.exists_code (RecursiveIn.iff_nat.mp hred)⟩

theorem extension_literal_join_program (I J : CountableIdeal)
    (hIJ : I.carrier ⊆ J.carrier) (ρ : I ≃o I) (σ : J ≃o J)
    (he : Extends hIJ ρ σ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (A R : Oracle) (hA : degree A ∈ J.carrier)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val) :
    ∃ X : Oracle, degree X = (σ ⟨degree A,hA⟩).val ∧ Reduces X (iterate (join A R) 5) ∧
      ∃ e : OracleCode,
        OracleCode.eval (oracleFunction (iterate (join A R) 5)) e = oracleFunction X := by
  let z : I := ⟨degree (jump FixedArithmetic.zero),hz⟩
  let zJ : ideal J := ⟨z.val,hIJ z.property⟩
  let x : ideal J := ⟨degree A,hA⟩
  have hpre : degree R = ((lift σ).symm zJ).val :=
    hR.trans (extends_symm he z).symm
  exact literal_join_program (lift σ) zJ x rfl A R rfl hpre

end TuringRigidity.ExtensionArithmeticRepresentative

end OAI

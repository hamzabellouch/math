import OAI.Computability.DegreeRigidity.Main

namespace OAI


namespace TuringRigidity.ManuscriptArithmeticRepresentation
open UniformArithmetic

theorem identity_graph_arith : Arith (fun O _ => O 0 = O 1) := by
  have h := (((Arith.query 0).iff (Arith.query 1)).comp _ right_primrec).all
  apply h.congr
  intro O v
  simp only [right,Nat.unpair_pair]
  exact ⟨fun h => funext (fun n => Bool.eq_iff_iff.mpr (h n)),fun h n => by rw [h]⟩

theorem arithmetic_representation (π : Degree ≃o Degree) :
    ∃ F : Oracle → Oracle, Arith (fun O _ => F (O 0) = O 1) ∧
      ∀ A : Oracle, degree (F A) = π (degree A) :=
  ⟨id,identity_graph_arith,fun A => (ManuscriptMain.rigidity π (degree A)).symm⟩

end TuringRigidity.ManuscriptArithmeticRepresentation

end OAI

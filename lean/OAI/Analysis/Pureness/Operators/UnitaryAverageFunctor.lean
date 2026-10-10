import OAI.Analysis.Pureness.Operators.UnitaryAverages

namespace OAI
noncomputable section
namespace CuntzPureness
variable {B E : Type*} [CStarAlgebra B] [CStarAlgebra E]

lemma unitaryAverage_starHom_map {n : ℕ} (Φ : B →⋆ₐ[ℂ] E) (u : Fin n → unitary B) (x : B) :
    Φ (unitaryAverage u x) =
      unitaryAverage (B := E) (fun i => Unitary.map (StarMonoidHom.ofClass Φ) (u i)) (Φ x) := by
  simp only [unitaryAverage,map_smul,map_sum,map_mul,map_star]
  rfl
end CuntzPureness

end

end OAI

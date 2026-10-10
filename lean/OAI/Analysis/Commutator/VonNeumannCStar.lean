import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.VonNeumannCStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance isClosed (M : VonNeumannAlgebra H) : IsClosed (M : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [←M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

instance smulMemClass : SMulMemClass (VonNeumannAlgebra H) ℂ (H →L[ℂ] H) where
  smul_mem {s} c _ hx := s.toStarSubalgebra.smul_mem hx c

instance cstarAlgebra (M : VonNeumannAlgebra H) : CStarAlgebra M :=
  StarSubalgebra.cstarAlgebra M

lemma sqrt_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) : CFC.sqrt T∈M := by
  change CFC.sqrt T∈M.carrier
  rw [←M.centralizer_centralizer']
  intro B hB
  exact ((show Commute T B from hB T hT).cfcₙ_nnreal NNReal.sqrt).eq.symm

instance starOrderedRing (M : VonNeumannAlgebra H) : StarOrderedRing M :=
  StarOrderedRing.of_nonneg_iff' (fun {x y} h z => (show (z : H →L[ℂ] H)+(x : H →L[ℂ] H)≤(z : H →L[ℂ] H)+(y : H →L[ℂ] H) from add_le_add_right (show (x : H →L[ℂ] H)≤(y : H →L[ℂ] H) from h) _)) (by
    intro T
    constructor
    · intro hT
      refine ⟨⟨CFC.sqrt (T : H →L[ℂ] H),sqrt_mem M T.property⟩,?_⟩
      apply Subtype.ext
      change (T : H →L[ℂ] H)=star (CFC.sqrt (T : H →L[ℂ] H))*CFC.sqrt (T : H →L[ℂ] H)
      rw [(CFC.sqrt_nonneg (T : H →L[ℂ] H)).star_eq,CFC.sqrt_mul_sqrt_self (T : H →L[ℂ] H) hT]
    · rintro ⟨S,rfl⟩
      exact (star_mul_self_nonneg (S : H →L[ℂ] H)))

end Kadison.VonNeumannCStar

end

end
end

end OAI

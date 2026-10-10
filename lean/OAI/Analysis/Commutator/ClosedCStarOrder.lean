import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.ClosedCStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem starOrderedRing (S : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (S:Set (H →L[ℂ] H))] : StarOrderedRing S :=
  StarOrderedRing.of_nonneg_iff' (fun {x y} h z => (show (z : H →L[ℂ] H)+(x : H →L[ℂ] H)≤(z : H →L[ℂ] H)+(y : H →L[ℂ] H) from add_le_add_right (show (x : H →L[ℂ] H)≤(y : H →L[ℂ] H) from h) _)) (by
    intro T
    constructor
    · intro hT
      have hm : CFC.sqrt (T : H →L[ℂ] H)∈S := by
        rw [CFC.sqrt_eq_real_sqrt (T : H →L[ℂ] H) hT]
        exact cfcₙ_mem (𝕜':=ℂ) Real.sqrt T.property
      refine ⟨⟨CFC.sqrt (T : H →L[ℂ] H),hm⟩,?_⟩
      apply Subtype.ext
      change (T : H →L[ℂ] H)=star (CFC.sqrt (T : H →L[ℂ] H))*CFC.sqrt (T : H →L[ℂ] H)
      rw [(CFC.sqrt_nonneg (T : H →L[ℂ] H)).star_eq,CFC.sqrt_mul_sqrt_self (T : H →L[ℂ] H) hT]
    · rintro ⟨T,rfl⟩
      exact (star_mul_self_nonneg (T : H →L[ℂ] H)))

end Kadison.ClosedCStar

end

end
end

end OAI

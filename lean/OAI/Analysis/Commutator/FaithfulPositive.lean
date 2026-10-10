import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped CStarAlgebra

namespace Kadison

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma faithfulStar_nonneg_iff (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ) (a : A) :
    0 ≤ φ a ↔ 0 ≤ a := by
  refine ⟨fun h => ?_,fun h => map_nonneg φ h⟩
  have hb : IsSelfAdjoint (φ a) := IsSelfAdjoint.of_nonneg h
  have ha : IsSelfAdjoint a := by
    apply hφ
    simpa only [map_star] using hb.star_eq
  apply (CFC.posPart_eq_self a).mp
  apply hφ
  rw [CFC.posPart_def]
  change φ.toNonUnitalStarAlgHom (cfcₙ (fun r : ℝ => r⁺) a)=φ a
  rw [φ.toNonUnitalStarAlgHom.map_cfcₙ (fun r : ℝ => r⁺) a (ha:=ha) (hφa:=hb)]
  exact (CFC.posPart_eq_self (φ a)).mpr h

end Kadison

end

end
end

end OAI

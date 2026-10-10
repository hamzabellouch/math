import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions

namespace OAI

noncomputable section

namespace KaplanskyConsequences

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def tracialStatePullback (f : A →⋆ₐ[ℂ] B) (τ : TracialState B) : TracialState A where
  functional := PositiveLinearMap.mk₀
    (τ.functional.toLinearMap.comp f.toAlgHom.toLinearMap)
    (fun x hx => by
      change 0 ≤ τ.functional (f x)
      exact τ.functional.map_nonneg (by simpa only [map_zero] using (OrderHomClass.mono f hx)))
  normalized := by change τ.functional (f 1) = 1; rw [map_one,τ.normalized]
  tracial a b := by
    change τ.functional (f (a*b)) = τ.functional (f (b*a))
    simp only [map_mul f]
    exact τ.tracial (f a) (f b)

lemma no_tracialState_of_map (f : A →⋆ₐ[ℂ] B) (hA : IsEmpty (TracialState A)) :
    IsEmpty (TracialState B) := ⟨fun τ => hA.false (tracialStatePullback f τ)⟩


end KaplanskyConsequences

end

end OAI

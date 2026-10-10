import Mathlib
import OAI.Analysis.Commutator.InfiniteAmplification

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.InfiniteAmplification

variable {ι H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

def mapEquiv (U : H ≃ₗᵢ[ℂ] G) : Space ι H ≃ₗᵢ[ℂ] Space ι G :=
  LinearIsometryEquiv.ofSurjective (mapIsometry U.toLinearIsometry) (fun x =>
    ⟨mapIsometry U.symm.toLinearIsometry x,by ext i; exact U.apply_symm_apply (x i)⟩)

omit [CompleteSpace H] [CompleteSpace G] in
@[simp] lemma mapEquiv_apply (U : H ≃ₗᵢ[ℂ] G) (x : Space ι H) (i : ι) :
    mapEquiv U x i=U (x i) := rfl

omit [CompleteSpace H] [CompleteSpace G] in
lemma mapEquiv_intertwines (U : H ≃ₗᵢ[ℂ] G) (S : H →L[ℂ] H) (T : G →L[ℂ] G)
    (hU : ∀ x,U (S x)=T (U x)) (x : Space ι H) : mapEquiv U (map S x)=map T (mapEquiv U x) := by
  ext i
  exact hU (x i)

end Kadison.InfiniteAmplification

end

end
end

end OAI

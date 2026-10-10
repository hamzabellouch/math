import Mathlib
import OAI.Analysis.Commutator.DerivationBoundTransfer
import OAI.Analysis.Commutator.StableUniversalAssembly

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {A H : Type*} [CStarAlgebra A] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : PartialOrder A := CStarAlgebra.spectralOrder A

local instance : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

theorem all_bounded_derivations_inner (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (D : A →L[ℂ] (H →L[ℂ] H))
    (hD : ∀ a b,D (a*b)=(D a).comp (σ b)+(σ a).comp (D b)) :
    ∃ V : H →L[ℂ] H,‖V‖≤(1+9368)^2*‖D‖ ∧
      ∀ a : A,D a=V.comp (σ a)-(σ a).comp V := by
  exact DerivationColumns.implementation_of_bicommutant_bound σ D hD (by norm_num : (0:ℝ)≤9368)
    (fun Y h hh X hX => CentralSpectral.universal_bound _ Y h hh X hX)

end Kadison

end

end
end

end OAI

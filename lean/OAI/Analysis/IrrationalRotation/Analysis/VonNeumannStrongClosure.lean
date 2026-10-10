import OAI.Analysis.IrrationalRotation.Operators.Commutant
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

namespace Invariant233

section Normed
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem centralizer_stronglyClosed (s : Set (H →L[ℂ] H)) :
    IsStronglyClosed (Subalgebra.centralizer ℂ s) := by
  unfold IsStronglyClosed
  have heq :
      {A : H →Lₚₜ[ℂ] H | strongOperatorUnderlying A ∈ Subalgebra.centralizer ℂ s} =
      ⋂ T ∈ s, {A : H →Lₚₜ[ℂ] H | ∀ x : H, T (A x) = A (T x)} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Subalgebra.mem_centralizer_iff]
    apply forall_congr'
    intro T
    apply forall_congr'
    intro _
    exact ContinuousLinearMap.ext_iff
  rw [heq]
  exact isClosed_biInter fun T _ => Commutant.isClosed_strong_commutant T

end Normed

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vonNeumannAlgebra_stronglyClosed (M : VonNeumannAlgebra H) :
    IsStronglyClosed M.toStarSubalgebra.toSubalgebra := by
  have heq : M.toStarSubalgebra.toSubalgebra =
      Subalgebra.centralizer ℂ (M.commutant : Set (H →L[ℂ] H)) := by
    apply SetLike.coe_injective
    change (M : Set (H →L[ℂ] H)) = _
    rw [Subalgebra.coe_centralizer, VonNeumannAlgebra.coe_commutant,
      M.centralizer_centralizer]
  rw [heq]
  exact centralizer_stronglyClosed _

end Hilbert
end Invariant233

end OAI

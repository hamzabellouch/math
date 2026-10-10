import OAI.Algebra.AuslanderReiten.Stable.StableExt
import OAI.Algebra.AuslanderReiten.Stable.SourceStableShift

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison
open CochainComplex CochainComplex.HomComplex

universe u

variable {k R : Type u} [CommRing k] [Ring R] [Algebra k R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

include k

theorem positiveExtVanish_of_fullHom
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (hL : ExactProjectiveComplex (chainOfCochain L))
    (h : ∀ n : ℕ, 0 < n → Subsingleton (CohomologyClass K L (n : ℤ))) :
    PositiveExtVanish R (Cokernel (chainOfCochain K) 0) (Cokernel (chainOfCochain L) 0) := by
  apply positiveExtVanish_of_stableCokernels hK
  intro n
  let := h (n + 1) (Nat.zero_lt_succ n)
  exact (fullHomSourceStableLinearEquiv (k := k) K L ((n + 1 : ℕ) : ℤ) hK hL).symm.injective.subsingleton

theorem not_projective_of_fullHom_nontrivial
    (hK : TotallyAcyclicComplex (chainOfCochain K))
    (h : Nontrivial (CohomologyClass K K 0)) :
    ¬ Module.Projective R (Cokernel (chainOfCochain K) 0) := by
  intro hp
  let := hK.finite 0
  let := hp
  have : Subsingleton (StableHom R (Cokernel (chainOfCochain K) 0)
      (Cokernel (chainOfCochain K) 0)) := ⟨fun a b =>
    (StableHom.eq_zero_of_projective_source a).trans (StableHom.eq_zero_of_projective_source b).symm⟩
  have : Subsingleton (CohomologyClass K K 0) :=
    (fullHomStableZeroLinearEquiv (k := k) K K hK hK.toExactProjectiveComplex).injective.subsingleton
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  exact hab (Subsingleton.elim a b)

end ArExplicit

end

end OAI

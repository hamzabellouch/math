import OAI.GroupTheory.FiniteLattice.SectionAction
import Mathlib.GroupTheory.Subgroup.Simple

namespace OAI

namespace FiniteLattice.CommonCore

variable (K T : Type*) [Group K] [Finite K] [Group T] [IsSimpleGroup T]

/-- Compatible extensions whose relative cores retain the inner automorphisms
have a unique common extension, and the common core retains the inner automorphisms. -/
def Statement (ι : Type*) [Finite ι] [Nonempty ι]
    (A : Subgroup K) (U : ι → Subgroup K) (hAU : ∀ i, A ≤ U i)
    (alpha : A →* MulAut T) (beta : ∀ i, U i →* MulAut T) : Prop :=
  (∃ x y : T, x * y ≠ y * x) →
  (⨆ i, U i) = ⊤ →
  (∀ i, ∀ a : A, beta i (Subgroup.inclusion (hAU i) a) = alpha a) →
  (∀ i, (MulAut.conj : T →* MulAut T).range ≤
    (((A.subgroupOf (U i)).normalCore.map (U i).subtype).comap A.subtype).map
      alpha) →
  (MulAut.conj : T →* MulAut T).range ≤
      (A.normalCore.comap A.subtype).map alpha ∧
    ∃! b : K →* MulAut T, ∀ i, ∀ u : U i, b u = beta i u

end FiniteLattice.CommonCore

end OAI

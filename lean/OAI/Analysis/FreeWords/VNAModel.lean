import Mathlib
import OAI.Analysis.FreeWords.ConjugateCopies

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance vnaClosed (V : VonNeumannAlgebra H) :
    IsClosed (V.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  rw [VonNeumannAlgebra.coe_toStarSubalgebra, ← V.centralizer_centralizer]
  exact Set.isClosed_centralizer _

local instance vnaOrder (V : VonNeumannAlgebra H) : PartialOrder V.toStarSubalgebra :=
  CStarAlgebra.spectralOrder _

local instance vnaStarOrder (V : VonNeumannAlgebra H) : StarOrderedRing V.toStarSubalgebra :=
  CStarAlgebra.spectralOrderedRing _

def NormalTrace (V : VonNeumannAlgebra H) (τ : V.toStarSubalgebra →ₚ[ℂ] ℂ) : Prop :=
  ∀ s : Set V.toStarSubalgebra, s.Nonempty → DirectedOn (· ≤ ·) s →
    BddAbove s → (∀ x ∈ s, 0 ≤ x) →
    ∀ x : V.toStarSubalgebra, IsLUB s x → IsLUB (τ '' s) (τ x)

def matrixWordSum (V : VonNeumannAlgebra H) {τ : V.toStarSubalgebra →ₚ[ℂ] ℂ}
    {r d : ℕ} (F : FreeMatrixCopies τ r d) (W : Sym (Fin d) r) : V.toStarSubalgebra :=
  ∑ a ∈ (Finset.univ : Finset (Fin r → Fin d)).filter
      (fun a => (List.ofFn a : Multiset (Fin d)) = (W : Multiset (Fin d))),
    ((List.ofFn (fun j => F.diagonal j (a j))).reverse).prod

end

end KKFreeWords
end

end OAI

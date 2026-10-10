import Mathlib
import OAI.Analysis.Commutator.FiniteStandardRepresented

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence CyclicColumns HilbertPadding

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type) [Fintype ι] [Nonempty ι] (h : ℕ) (hh : 1 ≤ h)

local instance finiteStandardMainInterfaceIndexDecidableEq : DecidableEq ι := Classical.decEq ι

local instance finiteStandardMainInterfaceColumnDecidableEq : DecidableEq (Fin h) := Classical.decEq (Fin h)

local instance finiteStandardMainInterfaceSumDecidableEq : DecidableEq (Fin h⊕ι) := Classical.decEq _

local instance finiteStandardMainInterfaceDoubledSumDecidableEq : DecidableEq ((Fin 2)×(Fin h⊕ι)) := Classical.decEq _

variable (M : VonNeumannAlgebra H) [Nontrivial M] (E : ℕ → Stage M)

variable (τ : M →ₚ[ℂ] ℂ) (hnormal : NormalGNS.BoundedWOTContinuous M τ)

variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)

variable (F : FreeCornerPosition (MatrixGNS.trace (ι:=(Fin 2)×(Fin h⊕ι)) τ) ω
  (matrixVonNeumann ((Fin 2)×(Fin h⊕ι)) (0,Sum.inl (⟨0,lt_of_lt_of_le Nat.zero_lt_one hh⟩ : Fin h)) (generated M E))
  (matrixInclusion ((Fin 2)×(Fin h⊕ι)) (0,Sum.inl (⟨0,lt_of_lt_of_le Nat.zero_lt_one hh⟩ : Fin h)) M (generated M E) (generated_le M E)))

include hnormal hω F in
theorem finite_standard_matrixOperator_bound
    (hE : Monotone (fun n => (E n).hom.range))
    (hirr : ∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M))
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (X : Matrix (Fin h) (Fin h) (SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι))
    (hX : ∀ i j,X i j∈finiteStandardAlgebra ι M τ) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖ ≤
      (3122*commutatorSeminorm (finiteStandardAlgebra ι M τ) Y)*‖matrixOperator h X‖ := by
  let k₀ : Fin h := ⟨0,lt_of_lt_of_le Nat.zero_lt_one hh⟩
  let : Nonempty (Fin h) := ⟨k₀⟩
  have represented := finite_standard_entrywise_bound ι (Fin h) k₀ M E τ hnormal ω hω
  change _ at represented F
  delta finiteStandardRepresentedDoubledSumDecidableEq
    finiteStandardMainInterfaceDoubledSumDecidableEq at represented F
  exact represented F hE hirr hτ hfaith h1 Y X hX

end Kadison.MatrixTower

end

end OAI

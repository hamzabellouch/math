import Mathlib
import OAI.Analysis.Commutator.FiniteStandardMainInterface
import OAI.Analysis.Commutator.MatrixFreePositionProducer

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator Topology

open Filter

namespace Kadison.MatrixTower

open OperatorAmplification TracialSequence CyclicColumns HilbertPadding

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M]

variable (τ : M →ₚ[ℂ] ℂ)

omit [Nontrivial M] in
theorem exists_irreducible_stage_tower [TopologicalSpace.SeparableSpace τ.GNS]
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M) :
    ∃ E : ℕ → Stage M, Monotone (fun n => (E n).hom.range) ∧
      (∀ n,n+1 ≤ Fintype.card (E n).I) ∧
      (∀ a : M,(∀ n b,(E n).hom b*a=a*(E n).hom b) → ∃ z : ℂ,a=z • (1:M)) := by
  obtain ⟨x,hx,hxden⟩ := exists_selfAdjoint_dense_sequence M τ
  let E := tower M τ hτ hnormal hfaith hone hfac hdiffuse x hx
  refine ⟨E,tower_increasing M τ hτ hnormal hfaith hone hfac hdiffuse x hx,
    tower_size M τ hτ hnormal hfaith hone hfac hdiffuse x hx,?_⟩
  intro a ha
  refine ⟨τ a,?_⟩
  exact scalar_of_commutes M τ hτ hone x hxden E
    (fun j _ hε => tower_requirement M τ hτ hnormal hfaith hone hfac hdiffuse x hx j hε)
    hfaith a ha

variable (ι : Type) [Fintype ι] [Nonempty ι]

local instance finiteStandardUnconditionalIndexDecidableEq : DecidableEq ι := Classical.decEq ι

theorem finite_standard_bound [TopologicalSpace.SeparableSpace τ.GNS]
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (h : ℕ) (hh : 1 ≤ h)
    (Y : SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι)
    (X : Matrix (Fin h) (Fin h) (SumSpace (H:=τ.GNS) ι →L[ℂ] SumSpace (H:=τ.GNS) ι))
    (hX : ∀ i j,X i j∈finiteStandardAlgebra ι M τ) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖ ≤
      (3122*commutatorSeminorm (finiteStandardAlgebra ι M τ) Y)*‖matrixOperator h X‖ := by
  obtain ⟨E,hE,hsize,hirr⟩ := exists_irreducible_stage_tower M τ hτ hnormal hfaith hone hfac hdiffuse
  let k₀ : Fin h := ⟨0,lt_of_lt_of_le Nat.zero_lt_one hh⟩
  let i₀ : (Fin 2)×(Fin h⊕ι) := (0,Sum.inl k₀)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨F⟩ := exists_matrix_freeCornerPosition ((Fin 2)×(Fin h⊕ι)) i₀ M E τ ω
    hE hsize hirr hτ hnormal hfaith hone hω
  have bound := finite_standard_matrixOperator_bound ι h hh M E τ hnormal ω hω
  change _ at bound F
  delta finiteStandardMainInterfaceDoubledSumDecidableEq
    matrixFreePositionProducerDecidableEq at bound F
  exact bound F hE hirr hτ hfaith hone Y X hX

end Kadison.MatrixTower

end

end OAI

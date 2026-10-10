import Mathlib
import OAI.Analysis.Commutator.DiffuseProjection
import OAI.Analysis.Commutator.FiniteStandardUnconditional
import OAI.Analysis.Commutator.IntertwinerMatrixTransfer
import OAI.Analysis.Commutator.IntertwinerSeminorm
import OAI.Analysis.Commutator.MainMatrix
import OAI.Analysis.Commutator.RepresentationMatrixNorm
import OAI.Analysis.Commutator.StandardTrace

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.NormalRepresentation

open OperatorAmplification IntertwinerCompression MatrixTower

private lemma diagonal_compression_bound
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (M : VonNeumannAlgebra H) (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hπ : Function.Injective π) (ι : Type) [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (Q : VonNeumannAlgebra (SumSpace (H := K) ι))
    (hrange : ∀ b ∈ Q, ∃ a : M, diagonal (H := K) ι (π a) = b)
    (h : ℕ)
    (hbound : ∀ (Z : SumSpace (H := K) ι →L[ℂ] SumSpace (H := K) ι)
      (B : Matrix (Fin h) (Fin h) (SumSpace (H := K) ι →L[ℂ] SumSpace (H := K) ι)),
      (∀ i j, B i j ∈ Q) →
      ‖diagonalAmplification h Z * matrixOperator h B -
        matrixOperator h B * diagonalAmplification h Z‖ ≤
        (3122 * commutatorSeminorm Q Z) * ‖matrixOperator h B‖)
    (T : H →L[ℂ] SumSpace (H := K) ι) (hcon : ‖T‖ ≤ 1)
    (hT : ∀ a : M, T.comp (a : H →L[ℂ] H) =
      (diagonal (H := K) ι (π a)).comp T)
    (Y : H →L[ℂ] H) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H))
    (hX : ∀ i j, X i j ∈ M)
    (hmem : ∀ a : M, diagonal (H := K) ι (π a) ∈ Q) :
    ‖diagonalAmplification h ((T.adjoint.comp T) * Y * (T.adjoint.comp T)) * matrixOperator h X -
      matrixOperator h X * diagonalAmplification h ((T.adjoint.comp T) * Y * (T.adjoint.comp T))‖ ≤
      (3122 * commutatorSeminorm M Y) * ‖matrixOperator h X‖ := by
  let ψ := (diagonal (H := K) ι).comp π
  have hψ : Function.Injective ψ := by
    intro a b hab
    apply hπ
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    ext x
    have he := congrArg (fun U : SumSpace (H := K) ι →L[ℂ] SumSpace (H := K) ι =>
      U (single ι i x) i) hab
    simpa only [ψ, StarAlgHom.comp_apply, diagonal_apply, single_apply, ite_true] using he
  have hsemi := seminorm_le M Q ψ hψ hrange T hcon hT Y
  let A : Matrix (Fin h) (Fin h) M := fun i j => ⟨X i j, hX i j⟩
  have hA : ∀ i j, ψ (A i j) ∈ Q := fun i j => hmem (A i j)
  have hb := hbound (transfer T Y) (fun i j => ψ (A i j)) hA
  have hp := pullback_matrix_commutator_norm_le M.toStarSubalgebra.subtype ψ T hT hcon h A (transfer T Y)
  rw [transfer_back] at hp
  refine hp.trans (hb.trans ?_)
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hsemi (by norm_num)
  · exact matrixOperator_subtype_norm_le M ψ h X hX
  · exact norm_nonneg _
  · exact mul_nonneg (by norm_num) (commutatorSeminorm_nonneg M Y)


variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M] (τ : M →ₚ[ℂ] ℂ)

variable (ι : Type) [Fintype ι] [Nonempty ι]

local instance finiteStandardCompressionDecidableEq : DecidableEq ι := Classical.decEq ι

theorem finite_standard_compression_bound [TopologicalSpace.SeparableSpace τ.GNS]
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (T : H →L[ℂ] SumSpace (H:=τ.GNS) ι) (hcon : ‖T‖≤1)
    (hT : ∀ a : M,T.comp (a:H →L[ℂ] H)=
      (diagonal (H:=τ.GNS) ι (τ.gnsStarAlgHom a)).comp T)
    (h : ℕ) (hh : 1≤h) (Y : H →L[ℂ] H)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
    ‖diagonalAmplification h ((T.adjoint.comp T)*Y*(T.adjoint.comp T))*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h ((T.adjoint.comp T)*Y*(T.adjoint.comp T))‖≤
      (3122*commutatorSeminorm M Y)*‖matrixOperator h X‖ := by
  apply diagonal_compression_bound M τ.gnsStarAlgHom
    (NormalGNS.gns_injective M τ hfaith) ι (finiteStandardAlgebra ι M τ)
    (fun b hb => (finiteStandard_range ι M τ hτ hnormal b).mp hb)
    h ?_ T hcon hT Y X hX
    (fun a => (finiteStandard_range ι M τ hτ hnormal _).mpr ⟨a, rfl⟩)
  intro Z B hB
  have bound := finite_standard_bound M τ ι hτ hnormal hfaith hone hfac hdiffuse
  exact bound h hh Z B hB

end Kadison.NormalRepresentation

end

end OAI

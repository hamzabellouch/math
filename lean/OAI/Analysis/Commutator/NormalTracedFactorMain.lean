import Mathlib
import OAI.Analysis.Commutator.AmplifiedStrongLimit
import OAI.Analysis.Commutator.BiprodLinkEmpty
import OAI.Analysis.Commutator.FiniteStandardCompression
import OAI.Analysis.Commutator.NormalRepresentationColumns

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.NormalRepresentation

open HilbertBiprod PartialIsometryOrder BiprodLinkColumn IntertwinerCompression

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) [Nontrivial M] (τ : M →ₚ[ℂ] ℂ)

theorem traced_factor_bound [TopologicalSpace.SeparableSpace τ.GNS]
    (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hfac : FactorCorner.IsFactor M) (hdiffuse : DiffuseProjection.HasNoMinimalProjections M)
    (h : ℕ) (hh : 1≤h) (Y : H →L[ℂ] H)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈M) :
    ‖diagonalAmplification h Y*matrixOperator h X-
      matrixOperator h X*diagonalAmplification h Y‖≤
      (3122*commutatorSeminorm M Y)*‖matrixOperator h X‖ := by
  classical
  let N := (diagonalAlgebra M τ hnormal).commutant
  obtain ⟨S,hS,hspan⟩ := exists_orthogonal_links M τ hnormal hfac hone
  let P : Finset S → H →L[ℂ] H := compression N S
  have hP (s : Finset S) : ‖P s‖≤1 := compression_norm_le N S hS s
  have hstrong (x : H) : Tendsto (fun s : Finset S => P s x) atTop (𝓝 x) :=
    compression_tendsto N S hS hspan x
  have hbound (s : Finset S) :
      ‖diagonalAmplification h (P s*Y*P s)*matrixOperator h X-
        matrixOperator h X*diagonalAmplification h (P s*Y*P s)‖≤
          (3122*commutatorSeminorm M Y)*‖matrixOperator h X‖ := by
    rcases s.eq_empty_or_nonempty with hs|hs
    · subst s
      have hz : P ∅=0 := compression_empty N S
      rw [hz,zero_mul,mul_zero]
      have hd : diagonalAmplification h (0:H →L[ℂ] H)=0 := by ext x i; rfl
      rw [hd,zero_mul,mul_zero,sub_zero,norm_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) (commutatorSeminorm_nonneg M Y)) (norm_nonneg _)
    · let : Nonempty s := ⟨⟨hs.choose,hs.choose_spec⟩⟩
      have hc := column_norm_le N S hS s
      have hi := finiteColumn_intertwines M τ hnormal S s
      have hb := finite_standard_compression_bound M τ s hτ hnormal hfaith hone hfac hdiffuse
        (finiteColumn N S s) hc hi h hh Y X hX
      have hsq : (finiteColumn N S s).adjoint.comp (finiteColumn N S s)=P s :=
        column_square N S s
      exact (congrArg (fun Q : H →L[ℂ] H =>
        ‖diagonalAmplification h (Q*Y*Q)*matrixOperator h X-
          matrixOperator h X*diagonalAmplification h (Q*Y*Q)‖ ≤
            (3122*commutatorSeminorm M Y)*‖matrixOperator h X‖) hsq).mp hb
  exact StrongContractionLimit.commutator_bound_limit
    (fun s : Finset S => P s*Y*P s) Y
    (StrongContractionLimit.sandwich_tendsto P hP hstrong Y) h X
    ((3122*commutatorSeminorm M Y)*‖matrixOperator h X‖)
    (mul_nonneg (mul_nonneg (by norm_num) (commutatorSeminorm_nonneg M Y)) (norm_nonneg _))
    (Filter.Eventually.of_forall hbound)

end Kadison.NormalRepresentation

end

end OAI

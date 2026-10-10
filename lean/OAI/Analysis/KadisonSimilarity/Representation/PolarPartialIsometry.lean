import OAI.Analysis.KadisonSimilarity.Representation.SpectralStepDischarge
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

namespace OAI

/-! # Concrete right supports in a finite tracial von Neumann algebra

The partial isometry is constructed by extending the isometry
`sqrt(x* x) ξ ↦ x ξ` from its dense range and setting it to zero on the
orthogonal complement. Bicommutant closure keeps that operator in the algebra.
-/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The range map, with its codomain restricted to the closed range. -/
def rangeIntoClosure (B : H →L[ℂ] H) : H →ₗ[ℂ] operatorRangeClosure B :=
  B.toLinearMap.codRestrict _ (fun x =>
    Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

omit [CompleteSpace H] in
theorem rangeIntoClosure_dense (B : H →L[ℂ] H) : DenseRange (rangeIntoClosure B) := by
  change Dense (Set.range (rangeIntoClosure B))
  rw [Subtype.dense_iff, ← Set.range_comp]
  exact Set.Subset.rfl

/-- Positive square root used only for this polar factor. -/
def polarModulus (x : H →L[ℂ] H) : H →L[ℂ] H := CFC.sqrt (star x * x)

theorem polarModulus_selfAdjoint (x : H →L[ℂ] H) : IsSelfAdjoint (polarModulus x) :=
  (CFC.sqrt_nonneg _).isSelfAdjoint

theorem polarModulus_square (x : H →L[ℂ] H) : polarModulus x * polarModulus x = star x * x :=
  CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg x)

theorem polarModulus_norm_apply (x : H →L[ℂ] H) (ξ : H) :
    ‖polarModulus x ξ‖ = ‖x ξ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  have he : (polarModulus x).adjoint.comp (polarModulus x) = x.adjoint.comp x := by
    change star (polarModulus x) * polarModulus x = star x * x
    rw [(polarModulus_selfAdjoint x).star_eq, polarModulus_square]
  rw [he]

/-- Isometry from the initial closed range to the ambient Hilbert space. -/
def polarRangeIsometry (x : H →L[ℂ] H) : operatorRangeClosure (polarModulus x) →ₗᵢ[ℂ] H :=
  x.toLinearMap.extendOfIsometry (rangeIntoClosure_dense (polarModulus x))
    (fun ξ => (polarModulus_norm_apply x ξ).symm)

@[simp] theorem polarRangeIsometry_apply (x : H →L[ℂ] H) (ξ : H) :
    polarRangeIsometry x (rangeIntoClosure (polarModulus x) ξ) = x ξ :=
  LinearMap.extendOfIsometry_eq _ _ _ _

/-- The actual partial isometry, extended by zero. -/
def polarPartialIsometry (x : H →L[ℂ] H) : H →L[ℂ] H :=
  (polarRangeIsometry x).toContinuousLinearMap.comp
    (operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto

theorem polarPartialIsometry_mul_modulus (x : H →L[ℂ] H) :
    polarPartialIsometry x * polarModulus x = x := by
  ext ξ
  have he : (operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto
      (polarModulus x ξ) = rangeIntoClosure (polarModulus x) ξ := by
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr
      (Submodule.le_topologicalClosure _ ⟨ξ, rfl⟩)
  change polarRangeIsometry x
    ((operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto (polarModulus x ξ)) = x ξ
  rw [he, polarRangeIsometry_apply]

theorem polarPartialIsometry_initial (x : H →L[ℂ] H) :
    star (polarPartialIsometry x) * polarPartialIsometry x = rangeSupport (polarModulus x) := by
  let M := operatorRangeClosure (polarModulus x)
  let J := (polarRangeIsometry x).toContinuousLinearMap
  let Q := M.orthogonalProjectionOnto
  change (J.comp Q).adjoint.comp (J.comp Q) = M.starProjection
  rw [ContinuousLinearMap.adjoint_comp]
  calc
    (Q.adjoint.comp J.adjoint).comp (J.comp Q) =
        Q.adjoint.comp ((J.adjoint.comp J).comp Q) := by simp only [ContinuousLinearMap.comp_assoc]
    _ = M.subtypeL.comp Q := by
      rw [(polarRangeIsometry x).adjoint_comp_self, ContinuousLinearMap.one_def,
        ContinuousLinearMap.id_comp, Submodule.adjoint_orthogonalProjectionOnto]
    _ = M.starProjection := rfl

theorem polarPartialIsometry_mul_initial (x : H →L[ℂ] H) :
    polarPartialIsometry x * rangeSupport (polarModulus x) = polarPartialIsometry x := by
  ext ξ
  change polarRangeIsometry x
      ((operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto
        ((operatorRangeClosure (polarModulus x)).starProjection ξ)) =
    polarRangeIsometry x ((operatorRangeClosure (polarModulus x)).orthogonalProjectionOnto ξ)
  congr 1
  apply Subtype.ext
  exact congrArg (fun T : H →L[ℂ] H => T ξ)
    (rangeSupport_isStarProjection (polarModulus x)).isIdempotentElem.eq

theorem polarPartialIsometry_final (x : H →L[ℂ] H) :
    IsStarProjection (polarPartialIsometry x * star (polarPartialIsometry x)) := by
  constructor
  · change (polarPartialIsometry x * star (polarPartialIsometry x)) *
      (polarPartialIsometry x * star (polarPartialIsometry x)) = _
    calc
      _ = (polarPartialIsometry x *
          (star (polarPartialIsometry x) * polarPartialIsometry x)) *
          star (polarPartialIsometry x) := by simp only [mul_assoc]
      _ = polarPartialIsometry x * star (polarPartialIsometry x) := by
        rw [polarPartialIsometry_initial, polarPartialIsometry_mul_initial]
  · exact IsSelfAdjoint.mul_star_self _

/-- A left support of x is also a left support of its polar partial isometry. -/
theorem leftSupport_polarPartialIsometry (x q : H →L[ℂ] H) (hqx : q * x = x) :
    q * polarPartialIsometry x = polarPartialIsometry x := by
  have he : ∀ ξ : operatorRangeClosure (polarModulus x),
      q (polarRangeIsometry x ξ) = polarRangeIsometry x ξ := by
    intro ξ
    refine (rangeIntoClosure_dense (polarModulus x)).induction ?_ ?_ ξ
    · rintro _ ⟨η, rfl⟩
      rw [polarRangeIsometry_apply]
      exact congrArg (fun T : H →L[ℂ] H => T η) hqx
    · exact isClosed_eq (q.continuous.comp (polarRangeIsometry x).continuous)
        (polarRangeIsometry x).continuous
  ext ξ
  exact he _

/-- Commutation on the two dense range maps extends to the polar isometry. -/
theorem polarPartialIsometry_commutes (x T : H →L[ℂ] H)
    (hx : Commute x T) (hS : Commute (polarModulus x) T)
    (hSstar : Commute (polarModulus x) (star T)) :
    Commute (polarPartialIsometry x) T := by
  let M := operatorRangeClosure (polarModulus x)
  let J := polarRangeIsometry x
  let Q := M.orthogonalProjectionOnto
  let R : M →L[ℂ] M := T.restrict (fun ξ hξ => operatorRangeClosure_invariant _ T hS hξ)
  have hJ : ∀ ξ : M, J (R ξ) = T (J ξ) := by
    intro ξ
    refine (rangeIntoClosure_dense (polarModulus x)).induction ?_ ?_ ξ
    · rintro _ ⟨η, rfl⟩
      have hR : R (rangeIntoClosure (polarModulus x) η) =
          rangeIntoClosure (polarModulus x) (T η) := by
        apply Subtype.ext
        exact (congrArg (fun S : H →L[ℂ] H => S η) hS.eq).symm
      rw [hR, polarRangeIsometry_apply, polarRangeIsometry_apply]
      exact congrArg (fun S : H →L[ℂ] H => S η) hx.eq
    · exact isClosed_eq (J.continuous.comp R.continuous) (T.continuous.comp J.continuous)
  have hQ (ξ : H) : Q (T ξ) = R (Q ξ) := by
    apply Subtype.ext
    exact congrArg (fun S : H →L[ℂ] H => S ξ) (rangeSupport_commutes _ T hS hSstar).eq
  change polarPartialIsometry x * T = T * polarPartialIsometry x
  ext ξ
  change J (Q (T ξ)) = T (J (Q ξ))
  rw [hQ, hJ]

theorem polarModulus_mem (P : VonNeumannAlgebra H) (x : H →L[ℂ] H) (hx : x ∈ P) :
    polarModulus x ∈ P := by
  let : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
    change IsClosed P.carrier
    rw [← P.centralizer_centralizer']
    exact Set.isClosed_centralizer _
  rw [polarModulus, CFC.sqrt_eq_real_sqrt (star x * x) (star_mul_self_nonneg x)]
  have hxstar : star x ∈ P.toStarSubalgebra := star_mem hx
  have hxx : star x * x ∈ P.toStarSubalgebra := P.toStarSubalgebra.mul_mem hxstar hx
  exact cfcₙ_mem (𝕜' := ℂ) (s := P.toStarSubalgebra) Real.sqrt hxx

theorem polarPartialIsometry_mem (P : VonNeumannAlgebra H) (x : H →L[ℂ] H) (hx : x ∈ P) :
    polarPartialIsometry x ∈ P := by
  suffices polarPartialIsometry x ∈ P.commutant.commutant by simpa using this
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  have hS := polarModulus_mem P x hx
  exact (polarPartialIsometry_commutes x T
    (VonNeumannAlgebra.mem_commutant_iff.mp hT x hx)
    (VonNeumannAlgebra.mem_commutant_iff.mp hT _ hS)
    (VonNeumannAlgebra.mem_commutant_iff.mp (star_mem hT) _ hS)).eq.symm

end KadisonSimilarity

end

end OAI

import OAI.Analysis.KadisonKastler.StatePreservingSpatial

namespace OAI

/-! # Bounded Radon--Nikodym operators for vector states

Domination of the two orbit norms extends the algebraic orbit map to a
bounded operator in the commutant. Its square gives the positive
Radon--Nikodym operator on the original cyclic representation.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def dominatedVectorIntertwiner (M : VonNeumannAlgebra H) (ξ η : H) : H →L[ℂ] H :=
  (algebraVectorMap M η).extendOfNorm (algebraVectorMap M ξ)

variable (ξ η : H) (hcyc : DenseRange (algebraVectorMap M ξ)) (C : ℝ)
  (hbound : ∀ a : Algebra M, ‖a.val η‖ ≤ C * ‖a.val ξ‖)

include hcyc hbound in
theorem dominatedVectorIntertwiner_orbit (a : Algebra M) :
    dominatedVectorIntertwiner M ξ η (a.val ξ) = a.val η :=
  LinearMap.extendOfNorm_eq hcyc ⟨C,hbound⟩ a

include hcyc hbound in
theorem dominatedVectorIntertwiner_vector : dominatedVectorIntertwiner M ξ η ξ = η := by
  simpa using dominatedVectorIntertwiner_orbit ξ η hcyc C hbound 1

include hcyc hbound in
theorem dominatedVectorIntertwiner_norm (hC : 0 ≤ C) :
    ‖dominatedVectorIntertwiner M ξ η‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le hcyc hC hbound

include hcyc hbound in
theorem dominatedVectorIntertwiner_commutant : dominatedVectorIntertwiner M ξ η ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  let b : Algebra M := ⟨a,ha⟩
  ext x
  change a (dominatedVectorIntertwiner M ξ η x) = dominatedVectorIntertwiner M ξ η (a x)
  apply hcyc.induction_on
    (p := fun x => a (dominatedVectorIntertwiner M ξ η x) =
      dominatedVectorIntertwiner M ξ η (a x)) x
  · exact isClosed_eq (a.continuous.comp (dominatedVectorIntertwiner M ξ η).continuous)
      ((dominatedVectorIntertwiner M ξ η).continuous.comp a.continuous)
  · intro c
    change a (dominatedVectorIntertwiner M ξ η (c.val ξ)) =
      dominatedVectorIntertwiner M ξ η ((b*c).val ξ)
    rw [dominatedVectorIntertwiner_orbit ξ η hcyc C hbound,
      dominatedVectorIntertwiner_orbit ξ η hcyc C hbound]
    rfl

include hcyc hbound in
theorem exists_positive_vectorState_derivative (hC : 0 ≤ C) :
    ∃ T : H →L[ℂ] H, T ∈ M.commutant ∧ 0 ≤ T ∧ ‖T‖ ≤ C^2 ∧
      ∀ a : Algebra M, inner ℂ η (a.val η) = inner ℂ ξ (T (a.val ξ)) := by
  let R := dominatedVectorIntertwiner M ξ η
  have hR : R ∈ M.commutant := dominatedVectorIntertwiner_commutant ξ η hcyc C hbound
  have hn : ‖R‖ ≤ C := dominatedVectorIntertwiner_norm ξ η hcyc C hbound hC
  refine ⟨star R*R,M.commutant.mul_mem
    (M.commutant.toStarSubalgebra.star_mem' hR) hR,star_mul_self_nonneg R,?_,?_⟩
  · calc
      ‖star R*R‖ = ‖R‖^2 := by rw [CStarRing.norm_star_mul_self]; ring
      _ ≤ C^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  · intro a
    change inner ℂ η (a.val η) = inner ℂ ξ (R.adjoint (R (a.val ξ)))
    rw [ContinuousLinearMap.adjoint_inner_right]
    rw [dominatedVectorIntertwiner_orbit ξ η hcyc C hbound,
      dominatedVectorIntertwiner_vector ξ η hcyc C hbound]

include hcyc in
theorem commutant_operator_eq_of_vector_coefficients
    {T S : H →L[ℂ] H} (hT : T ∈ M.commutant) (hS : S ∈ M.commutant)
    (hcoeff : ∀ a : Algebra M, inner ℂ ξ (T (a.val ξ)) = inner ℂ ξ (S (a.val ξ))) :
    T = S := by
  have hv : T ξ = S ξ := by
    apply ext_inner_left ℂ
    intro y
    apply hcyc.induction_on
      (p := fun y => inner ℂ y (T ξ) = inner ℂ y (S ξ)) y
    · exact isClosed_eq (continuous_id.inner continuous_const)
        (continuous_id.inner continuous_const)
    · intro a
      change inner ℂ (a.val ξ) (T ξ) = inner ℂ (a.val ξ) (S ξ)
      rw [← ContinuousLinearMap.adjoint_inner_right,
        ← ContinuousLinearMap.adjoint_inner_right]
      have ht := congrArg (fun R : H →L[ℂ] H => R ξ)
        (VonNeumannAlgebra.mem_commutant_iff.mp hT (star a).val (star a).property)
      have hs := congrArg (fun R : H →L[ℂ] H => R ξ)
        (VonNeumannAlgebra.mem_commutant_iff.mp hS (star a).val (star a).property)
      change star a.val (T ξ) = T (star a.val ξ) at ht
      change star a.val (S ξ) = S (star a.val ξ) at hs
      change inner ℂ ξ (star a.val (T ξ)) = inner ℂ ξ (star a.val (S ξ))
      rw [ht,hs]
      exact hcoeff (star a)
  ext y
  apply hcyc.induction_on (p := fun y => T y = S y) y
  · exact isClosed_eq T.continuous S.continuous
  · intro a
    change T (a.val ξ) = S (a.val ξ)
    have ht := congrArg (fun R : H →L[ℂ] H => R ξ)
      (VonNeumannAlgebra.mem_commutant_iff.mp hT a.val a.property)
    have hs := congrArg (fun R : H →L[ℂ] H => R ξ)
      (VonNeumannAlgebra.mem_commutant_iff.mp hS a.val a.property)
    change a.val (T ξ) = T (a.val ξ) at ht
    change a.val (S ξ) = S (a.val ξ) at hs
    rw [← ht,← hs,hv]

include hcyc in
/-- The quadratic state inequality supplies the orbit norm bound directly. -/
theorem exists_positive_vectorState_derivative_of_quadratic_bound
    (D : ℝ) (hD : 0 ≤ D)
    (hdom : ∀ a : Algebra M,
      (inner ℂ η ((star a*a).val η)).re ≤ D * (inner ℂ ξ ((star a*a).val ξ)).re) :
    ∃ T : H →L[ℂ] H, T ∈ M.commutant ∧ 0 ≤ T ∧ ‖T‖ ≤ D ∧
      ∀ a : Algebra M, inner ℂ η (a.val η) = inner ℂ ξ (T (a.val ξ)) := by
  have hb (a : Algebra M) : ‖a.val η‖ ≤ Real.sqrt D * ‖a.val ξ‖ := by
    have h := hdom a
    change (inner ℂ η (a.val.adjoint (a.val η))).re ≤
      D * (inner ℂ ξ (a.val.adjoint (a.val ξ))).re at h
    rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right,
      ← RCLike.re_eq_complex_re,
      ← norm_sq_eq_re_inner,← norm_sq_eq_re_inner] at h
    have hp : 0 ≤ Real.sqrt D * ‖a.val ξ‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    apply (sq_le_sq₀ (norm_nonneg _) hp).mp
    rwa [mul_pow,Real.sq_sqrt hD]
  obtain ⟨T,hTM,hT,hbound,hstate⟩ := exists_positive_vectorState_derivative
    ξ η hcyc (Real.sqrt D) hb (Real.sqrt_nonneg D)
  exact ⟨T,hTM,hT,(Real.sq_sqrt hD) ▸ hbound,hstate⟩

end

end KadisonKastler

end OAI

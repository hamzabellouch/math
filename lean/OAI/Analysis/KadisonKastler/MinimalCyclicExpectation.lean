import OAI.Analysis.KadisonKastler.FiniteMatrixInjectivity

namespace OAI

/-! # Explicit retractions through a minimal cyclic space

The compression proof of type-I injectivity gives a specific contractive
retraction. Its coefficients on the minimal cyclic space agree with the
original ambient operator. These identities allow the trace-preserving
finite-stage construction to retain the original vector state.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (N : VonNeumannAlgebra H) (hN : ScalarCenter N)
  (p : AlgebraProjection N) (hp : IsMinimalProjectionIn N p)
  (ξ : H) (hξ : ξ ≠ 0) (hpξ : p.val.val ξ = ξ)

theorem typeICyclicEquiv_symm_norm (T : typeICyclicSpace N ξ →L[ℂ] typeICyclicSpace N ξ) :
    ‖(typeICyclicEquiv hN p hp ξ hξ hpξ).symm T‖ = ‖T‖ := by
  rw [← typeICyclicHom_norm hN p hp ξ hξ hpξ]
  change ‖typeICyclicEquiv hN p hp ξ hξ hpξ
    ((typeICyclicEquiv hN p hp ξ hξ hpξ).symm T)‖ = ‖T‖
  rw [(typeICyclicEquiv hN p hp ξ hξ hpξ).apply_symm_apply]

/-- The concrete ambient-to-algebra retraction supplied by a minimal projection. -/
def minimalCyclicRetraction : (H →L[ℂ] H) →L[ℂ] Algebra N := by
  let e := typeICyclicEquiv hN p hp ξ hξ hpξ
  let F : (H →L[ℂ] H) →ₗ[ℂ] Algebra N :=
    e.symm.toAlgEquiv.toLinearMap.comp (cornerCompression (typeICyclicSpace N ξ))
  exact F.mkContinuous 1 (fun T => by
    change ‖e.symm (cornerCompression (typeICyclicSpace N ξ) T)‖ ≤ 1 * ‖T‖
    rw [typeICyclicEquiv_symm_norm, one_mul]
    exact norm_cornerCompression_le _ T)

@[simp] theorem minimalCyclicRetraction_compression (T : H →L[ℂ] H) :
    typeICyclicHom ξ (minimalCyclicRetraction N hN p hp ξ hξ hpξ T) =
      cornerCompression (typeICyclicSpace N ξ) T := by
  change typeICyclicEquiv hN p hp ξ hξ hpξ
    ((typeICyclicEquiv hN p hp ξ hξ hpξ).symm
      (cornerCompression (typeICyclicSpace N ξ) T)) = _
  exact (typeICyclicEquiv hN p hp ξ hξ hpξ).apply_symm_apply _

theorem minimalCyclicRetraction_norm :
    ‖minimalCyclicRetraction N hN p hp ξ hξ hpξ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  change ‖(typeICyclicEquiv hN p hp ξ hξ hpξ).symm
    (cornerCompression (typeICyclicSpace N ξ) T)‖ ≤ 1 * ‖T‖
  rw [typeICyclicEquiv_symm_norm, one_mul]
  exact norm_cornerCompression_le _ T

@[simp] theorem minimalCyclicRetraction_fixed (a : Algebra N) :
    minimalCyclicRetraction N hN p hp ξ hξ hpξ a.val = a := by
  apply (typeICyclicEquiv hN p hp ξ hξ hpξ).injective
  change typeICyclicHom ξ (minimalCyclicRetraction N hN p hp ξ hξ hpξ a.val) =
    typeICyclicHom ξ a
  rw [minimalCyclicRetraction_compression, typeICyclicHom_eq_compression]

/-- Compression preserves every coefficient with both vectors in the cyclic space. -/
theorem minimalCyclicRetraction_coefficient (T : H →L[ℂ] H)
    (x y : typeICyclicSpace N ξ) :
    inner ℂ y.val ((minimalCyclicRetraction N hN p hp ξ hξ hpξ T).val x.val) =
      inner ℂ y.val (T x.val) := by
  have h := congrArg (fun A : typeICyclicSpace N ξ →L[ℂ] typeICyclicSpace N ξ =>
    inner ℂ y (A x)) (minimalCyclicRetraction_compression N hN p hp ξ hξ hpξ T)
  change inner ℂ y.val ((minimalCyclicRetraction N hN p hp ξ hξ hpξ T).val x.val) =
    inner ℂ y (cornerCompression (typeICyclicSpace N ξ) T x) at h
  simpa only [cornerCompression_apply,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using h

/-- The compression retraction respects left multiplication from its range. -/
theorem minimalCyclicRetraction_mul_left (a : Algebra N) (T : H →L[ℂ] H) :
    minimalCyclicRetraction N hN p hp ξ hξ hpξ (a.val * T) =
      a * minimalCyclicRetraction N hN p hp ξ hξ hpξ T := by
  apply (typeICyclicEquiv hN p hp ξ hξ hpξ).injective
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y.val
    ((minimalCyclicRetraction N hN p hp ξ hξ hpξ (a.val * T)).val x.val) =
      inner ℂ y.val (a.val ((minimalCyclicRetraction N hN p hp ξ hξ hpξ T).val x.val))
  rw [minimalCyclicRetraction_coefficient]
  let y' : typeICyclicSpace N ξ :=
    ⟨(star a).val y.val, vectorOrbitClosure_invariant _ _ (star a) y.property⟩
  have h := minimalCyclicRetraction_coefficient N hN p hp ξ hξ hpξ T x y'
  change inner ℂ (star a.val y.val)
    ((minimalCyclicRetraction N hN p hp ξ hξ hpξ T).val x.val) =
      inner ℂ (star a.val y.val) (T x.val) at h
  simpa only [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left, mul_apply_eq_comp] using h.symm

end

end KadisonKastler

end OAI

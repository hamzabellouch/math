import OAI.Analysis.KadisonSimilarity.Representation.ConcretePredualDuality
import OAI.Analysis.KadisonSimilarity.Tracial.PredualGNSNormality
import OAI.Analysis.BoundedHochschild.NormalTraceFaithfulness

namespace OAI

/-! Faithful normal tracial states on concrete finite factors. The only
structural assumptions are finiteness and a scalar center. -/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexOrder
open BoundedHochschild BoundedHochschild.KadisonRingrose

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

def vectorPositiveFunctional (ξ : H) : M.toStarSubalgebra →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (normalCoefficient M ξ ξ).toLinearMap (fun a ha => by
    have hp : (a : H →L[ℂ] H).IsPositive :=
      ContinuousLinearMap.nonneg_iff_isPositive.mp ha
    exact hp.inner_nonneg_right ξ)

@[simp] theorem vectorPositiveFunctional_apply (ξ : H) (a : M.toStarSubalgebra) :
    vectorPositiveFunctional M ξ a = inner ℂ ξ ((a : H →L[ℂ] H) ξ) := rfl

theorem vectorPositiveFunctional_normal (ξ : H) :
    TraceInPredual (concretePredualEquiv M) (vectorPositiveFunctional M ξ) := by
  refine ⟨predualCoefficient M ξ ξ, fun a => ?_⟩
  rw [concretePredualEquiv_symm_apply, predualCoefficient_apply,
    vectorPositiveFunctional_apply]
  calc
    inner ℂ ξ ((a : H →L[ℂ] H) ξ) =
        inner ℂ ((a : H →L[ℂ] H).adjoint ξ) ξ :=
      (ContinuousLinearMap.adjoint_inner_left (a : H →L[ℂ] H) ξ ξ).symm
    _ = _ := (inner_conj_symm (𝕜 := ℂ) _ _).symm

theorem vectorPositiveFunctional_one (ξ : H) (hξ : ‖ξ‖ = 1) :
    vectorPositiveFunctional M ξ 1 = 1 := by
  rw [vectorPositiveFunctional_apply]
  change inner ℂ ξ ξ = 1
  rw [inner_self_eq_norm_sq_to_K, hξ]
  norm_num

/-- Finiteness gives a normalized normal trace; a scalar center makes it
faithful. This constructs the finite-factor trace rather than assuming it. -/
theorem exists_faithful_normal_trace [Nontrivial H]
    (hfinite : FiniteAlgebra M.toStarSubalgebra)
    (hfactor : ∀ a : M.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ M.toStarSubalgebra c) :
    ∃ τ : M.toStarSubalgebra →ₚ[ℂ] ℂ,
      TraceInPredual (concretePredualEquiv M) τ ∧ τ 1 = 1 ∧
      (∀ a b, τ (a * b) = τ (b * a)) ∧
      (∀ a, τ (star a * a) = 0 → a = 0) ∧ HasNormalGNS τ := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  let ξ := (‖x‖⁻¹ : ℝ) • x
  have hξ : ‖ξ‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  obtain ⟨τ, hτ, hτ1, htr, _⟩ := exists_normal_tracial_average (concretePredualEquiv M)
    hfinite (vectorPositiveFunctional M ξ) (vectorPositiveFunctional_normal M ξ)
  have h1 : τ 1 = 1 := hτ1.trans (vectorPositiveFunctional_one M ξ hξ)
  refine ⟨τ, hτ, h1, htr, normal_trace_faithful_of_center
    (concretePredualEquiv M) τ hτ htr ?_,
    hasNormalGNS_of_predual (concretePredualEquiv M) τ hτ htr⟩
  intro p _ hcentral hp
  obtain ⟨c, rfl⟩ := hfactor p hcentral
  have hc : c = 0 := by
    simpa only [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_eq_mul, mul_one] using hp
  rw [hc, map_zero]

/-- A fixed choice of the normalized normal trace, for the subsequent
hyperfinite-subfactor construction. -/
def finiteFactorTrace [Nontrivial H]
    (hfinite : FiniteAlgebra M.toStarSubalgebra)
    (hfactor : ∀ a : M.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ M.toStarSubalgebra c) :
    M.toStarSubalgebra →ₚ[ℂ] ℂ :=
  (exists_faithful_normal_trace M hfinite hfactor).choose

theorem finiteFactorTrace_spec [Nontrivial H]
    (hfinite : FiniteAlgebra M.toStarSubalgebra)
    (hfactor : ∀ a : M.toStarSubalgebra, (∀ b, a * b = b * a) →
      ∃ c : ℂ, a = algebraMap ℂ M.toStarSubalgebra c) :
    let τ := finiteFactorTrace M hfinite hfactor
    TraceInPredual (concretePredualEquiv M) τ ∧ τ 1 = 1 ∧
      (∀ a b, τ (a * b) = τ (b * a)) ∧
      (∀ a, τ (star a * a) = 0 → a = 0) ∧ HasNormalGNS τ :=
  (exists_faithful_normal_trace M hfinite hfactor).choose_spec

end KadisonSimilarity

end

end OAI

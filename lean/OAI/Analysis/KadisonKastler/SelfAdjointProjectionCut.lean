import OAI.Analysis.KadisonKastler.FiniteAlgebraCutSelection
import OAI.Analysis.KadisonKastler.BoundedSpectralApproximation
import OAI.Analysis.KadisonKastler.ConjugationFunctionalCalculus

namespace OAI

/-! # A projection cut from an almost-central self-adjoint contraction

Finite spectral approximations preserve the strict energy inequality.
The finite threshold selection then supplies a projection in the original
algebra, with both the reference-vector and test-vector bounds.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_selfAdjoint_projection_cut
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (a : Algebra M) (ha : IsSelfAdjoint a) (han : ‖a‖ ≤ 1)
    (ξ η : H) (hη : ‖η‖ = 1) (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b)
    (hsmall : ‖(a.val - conjugationOperator J a.val) ξ‖ * ‖ξ‖ <
      δ * (‖(a.val - conjugationOperator J a.val) η‖ ^ 2 / 2 - 2 * b)) :
    ∃ p : AlgebraProjection M,
      ‖(p.val.val - conjugationOperator J p.val.val) ξ‖ ^ 2 ≤ δ ∧
      b ≤ ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by
  let F (A : H →L[ℂ] H) := ‖(A - conjugationOperator J A) ξ‖ * ‖ξ‖ -
    δ * (‖(A - conjugationOperator J A) η‖ ^ 2 / 2 - 2 * b)
  have hC : Continuous (conjugationOperator J : (H →L[ℂ] H) → (H →L[ℂ] H)) :=
    (conjugationRealStarAlgEquiv_isometry J hJ).continuous
  have hV (ζ : H) : Continuous (fun A : H →L[ℂ] H => (A - conjugationOperator J A) ζ) :=
    (continuous_id.sub hC).clm_apply continuous_const
  have hF : Continuous F := by
    exact ((hV ξ).norm.mul continuous_const).sub
      (continuous_const.mul (((hV η).norm.pow 2).div_const 2 |>.sub continuous_const))
  have hFa : F a.val < 0 := sub_neg.mpr hsmall
  have hnear : ∀ᶠ A in 𝓝 a.val, F A < 0 := hF.continuousAt.eventually_lt_const hFa
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨Q,c,hcr,happrox⟩ := exists_bounded_spectral_approximation a ha han ε hε
  let r : Algebra M := ∑ i, (c i : ℂ) • (Q.piece i).val
  change ‖a-r‖ < ε at happrox
  have hdist : dist r.val a.val < ε := by
    rw [dist_eq_norm,norm_sub_rev]
    exact happrox
  have hs := hball hdist
  have hr : r.val = ∑ i, (c i : ℂ) • (Q.piece i).val.val := by
    change M.toStarSubalgebra.subtype (∑ i, (c i : ℂ) • (Q.piece i).val) = _
    simp only [map_sum,map_smul]
    rfl
  have htotal : (∑ i, (Q.piece i).val) = 1 := Q.total
  apply exists_finite_algebra_projection_cut J hJ hright Q.piece Q.orthogonal htotal c hcr
    ξ η hη δ b hδ hb
  rw [← hr]
  exact sub_neg.mp hs

theorem exists_projection_gap_of_selfAdjoint
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (a : Algebra M) (ha : IsSelfAdjoint a) (han : ‖a‖ ≤ 1)
    (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ‖(a.val - conjugationOperator J a.val) ξ‖ < δ / 16)
    (hgap : (1 / 2 : ℝ) ≤ ‖(a.val - conjugationOperator J a.val) η‖) :
    ∃ p : AlgebraProjection M,
      ‖(p.val.val - conjugationOperator J p.val.val) ξ‖ ^ 2 ≤ δ ∧
      (1 / 32 : ℝ) ≤ ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by
  apply exists_selfAdjoint_projection_cut J hJ hright a ha han ξ η hη δ (1 / 32)
    hδ (by norm_num)
  rw [hξ,mul_one]
  have hh : (1 / 16 : ℝ) ≤ ‖(a.val - conjugationOperator J a.val) η‖ ^ 2 / 2 -
      2 * (1 / 32 : ℝ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hh hδ.le
  nlinarith

end

end KadisonKastler

end OAI

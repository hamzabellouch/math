import OAI.Analysis.KadisonKastler.ConjugateOutwardCuts
import OAI.Analysis.KadisonKastler.BoundedSpectralApproximation
import OAI.Analysis.KadisonKastler.ConjugationFunctionalCalculus

namespace OAI

/-! # Passing two-vector cut inequalities to a self-adjoint operator

Finite spectral approximation retains the strict energy inequality.
There is no operator-norm bound in the resulting projection theorem.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_selfAdjoint_two_vector_projection
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (a : Algebra M) (ha : IsSelfAdjoint a)
    (ξ η : H) (hξ : J ξ=ξ) {α K : ℝ} (hα : 0 < α) (hK : 0 < K)
    (hsmall : α*(‖a.val ξ‖^2+‖a.val η‖^2)+
      2*K*‖a.val ξ‖*‖(a.val-conjugationOperator J a.val) ξ‖ <
        α*K/2*‖(a.val-conjugationOperator J a.val) η‖^2) :
    ∃ p : AlgebraProjection M,
      ‖p.val.val ξ‖^2+‖p.val.val η‖^2 < K*‖centralVectorDefect J η p.val.val‖^2 ∧
      ‖centralVectorDefect J ξ p.val.val‖^2 < α*‖centralVectorDefect J η p.val.val‖^2 := by
  let F (A : H →L[ℂ] H) := α*(‖A ξ‖^2+‖A η‖^2)+
    2*K*‖A ξ‖*‖(A-conjugationOperator J A) ξ‖-
      α*K/2*‖(A-conjugationOperator J A) η‖^2
  have hC : Continuous (conjugationOperator J : (H →L[ℂ] H) → (H →L[ℂ] H)) :=
    (conjugationRealStarAlgEquiv_isometry J hJ).continuous
  have hV (ζ : H) : Continuous (fun A : H →L[ℂ] H => (A-conjugationOperator J A) ζ) :=
    (continuous_id.sub hC).clm_apply continuous_const
  have hA (ζ : H) : Continuous (fun A : H →L[ℂ] H => A ζ) :=
    continuous_id.clm_apply continuous_const
  have hF : Continuous F :=
    ((continuous_const.mul (((hA ξ).norm.pow 2).add ((hA η).norm.pow 2))).add
      ((continuous_const.mul (hA ξ).norm).mul (hV ξ).norm)).sub
        (continuous_const.mul ((hV η).norm.pow 2))
  have hnear : ∀ᶠ A in 𝓝 a.val, F A < 0 :=
    hF.continuousAt.eventually_lt_const (sub_neg.mpr hsmall)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨Q,c,_,happrox⟩ := exists_finite_spectral_approximation
    (identityProjection M) a ha ε hε
  let r : Algebra M := ∑ i, (c i : ℂ) • (Q.piece i).val
  have hr : ‖a-r‖ < ε := by
    change ‖(1 : Algebra M)*a*1-r‖ < ε at happrox
    simpa only [one_mul,mul_one] using happrox
  have hdist : dist r.val a.val < ε := by
    rw [dist_eq_norm,norm_sub_rev]
    exact hr
  have hs := sub_neg.mp (hball hdist)
  have hre : r.val=∑ i, (c i : ℂ) • (Q.piece i).val.val := by
    change M.toStarSubalgebra.subtype (∑ i, (c i : ℂ) • (Q.piece i).val)=_
    simp only [map_sum,map_smul]
    rfl
  apply exists_finite_two_vector_projection J hJ hright Q.piece Q.orthogonal Q.total
    c ξ η hξ hα hK
  rw [← hre]
  exact hs

end

end KadisonKastler

end OAI

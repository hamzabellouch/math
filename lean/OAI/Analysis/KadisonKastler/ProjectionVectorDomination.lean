import OAI.Analysis.KadisonKastler.CornerStateWeights
import OAI.Analysis.FactorGeneration.SpectralStates

namespace OAI

/-! # Detecting failure of vector-state domination on a projection

Finite positive spectral approximation extends inequalities on projections
to positive operators. Consequently a failure of bounded orbit domination
is witnessed on a genuine algebra projection, at any prescribed ratio.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance projectionDominationOrder : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance projectionDominationLE : LE (Algebra M) :=
  (CStarAlgebra.spectralOrder (Algebra M)).toLE
local instance projectionDominationStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem vector_quadratic_bound_of_projection_bound (ξ η : H) (C : ℝ)
    (hproj : ∀ p : AlgebraProjection M, ‖p.val.val η‖^2 ≤ C*‖p.val.val ξ‖^2) :
    ∀ a : Algebra M, ‖a.val η‖^2 ≤ C*‖a.val ξ‖^2 := by
  let F : Algebra M →L[ℝ] ℝ :=
    Complex.reCLM.comp ((vectorFunctional η).restrictScalars ℝ)-
      C • Complex.reCLM.comp ((vectorFunctional ξ).restrictScalars ℝ)
  have hF (a : Algebra M) : F a=(vectorFunctional η a).re-C*(vectorFunctional ξ a).re := rfl
  have hp (p : AlgebraProjection M) : F p.val ≤ 0 := by
    rw [hF,vectorFunctional_projection,vectorFunctional_projection]
    simp only [Complex.ofReal_re,projectionVectorWeight]
    exact sub_nonpos.mpr (hproj p)
  have hpos (x : Algebra M) (hx : 0 ≤ x) : F x ≤ 0 := by
    by_contra hn
    have hxF : 0 < F x := lt_of_not_ge hn
    have hnear := F.continuous.continuousAt.eventually (Ioi_mem_nhds hxF)
    obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hnear
    obtain ⟨Q,c,hc,_,happrox⟩ := exists_positive_spectral_approximation x hx ε hε
    let r : Algebra M := ∑ i, c i • (Q.piece i).val
    have hr : ‖x-r‖ < ε := by
      simpa only [Complex.coe_smul] using happrox
    have hdist : dist r x < ε := by rw [dist_eq_norm,norm_sub_rev]; exact hr
    have hrpos : 0 < F r := hball hdist
    have hrnonpos : F r ≤ 0 := by
      change F (∑ i, c i • (Q.piece i).val) ≤ 0
      rw [map_sum]
      apply Finset.sum_nonpos
      intro i _
      rw [map_smul,smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (hc i) (hp (Q.piece i))
    exact (not_lt_of_ge hrnonpos) hrpos
  intro a
  have he := hpos (star a*a) (star_mul_self_nonneg a)
  rw [hF] at he
  change (inner ℂ η (a.val.adjoint (a.val η))).re-
    C*(inner ℂ ξ (a.val.adjoint (a.val ξ))).re ≤ 0 at he
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right] at he
  change RCLike.re (inner ℂ (a.val η) (a.val η))-
    C*RCLike.re (inner ℂ (a.val ξ) (a.val ξ)) ≤ 0 at he
  rw [inner_self_eq_norm_sq,inner_self_eq_norm_sq] at he
  exact sub_nonpos.mp he

theorem exists_projection_large_vector_ratio (ξ η : H)
    (hnot : ¬ ∃ C : ℝ, ∀ a : Algebra M, ‖a.val η‖ ≤ C*‖a.val ξ‖)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ p : AlgebraProjection M, R*‖p.val.val ξ‖^2 < ‖p.val.val η‖^2 := by
  by_contra hn
  push Not at hn
  have hb := vector_quadratic_bound_of_projection_bound ξ η R hn
  apply hnot
  refine ⟨Real.sqrt R,?_⟩
  intro a
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hR]
  exact hb a

end

end KadisonKastler

end OAI

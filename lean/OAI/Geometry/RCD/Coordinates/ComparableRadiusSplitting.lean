import OAI.Geometry.RCD.Coordinates.ComparableRadiusNormalization
import OAI.Geometry.RCD.Coordinates.NormalizedOuterDirectionError
import OAI.Geometry.RCD.Sobolev.HarmonicL1GradientBound
import OAI.Geometry.RCD.Harmonic.DirectionalToGramError
import OAI.Geometry.RCD.Harmonic.ColumnRepresentatives

namespace OAI

/-! # Full transformed splitting estimates at comparable radii

This is the analytic one-step part of transformation. The all-scale
geometric propagation is not assumed or asserted here.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.interior_radius_splitting {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (β : ℝ) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : X) (R : ℝ), 0 < R → -1 ≤ K*(2*R)^2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) δ u v →
      ∀ t : ℝ, τ*R ≤ t → t ≤ R → ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p t β
          (transformedColumn (hausdorff n X) hX.quadratic u A)
          (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
        IsExactMeanNormalization (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u) (ball p t) measurableSet_ball A := by
  obtain ⟨C,hC,hnormalize⟩ := hX.interior_radius_normalization hn τ hτ hτ1
  obtain ⟨θ,hθ,hsharp⟩ := hX.harmonic_l1_gradient_bound hn β (8*(n : ℝ)^2) hβ (by positivity)
  let D := 8*(n : ℝ)^2*C+1
  have ha : 0 ≤ (n : ℝ)^2*C := mul_nonneg (sq_nonneg _) (zero_le_one.trans hC)
  have hD : 0 < D := by dsimp only [D]; nlinarith
  let δ := min 1 (min ((1/2)/D) (min (β/D) (θ/D)))
  have hδ : 0 < δ := lt_min zero_lt_one
    (lt_min (div_pos (by norm_num) hD) (lt_min (div_pos hβ hD) (div_pos hθ hD)))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hhalf : D*δ ≤ 1/2 := by
    have hh : δ ≤ (1/2)/D := (min_le_right _ _).trans (min_le_left _ _)
    nlinarith [(le_div_iff₀ hD).mp hh]
  have hbet : D*δ ≤ β := by
    have hh : δ ≤ β/D := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    nlinarith [(le_div_iff₀ hD).mp hh]
  have htheta : D*δ ≤ θ := by
    have hh : δ ≤ θ/D := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    nlinarith [(le_div_iff₀ hD).mp hh]
  have hsmall : (n : ℝ)^2*(C*δ) ≤ 1/2 := by dsimp only [D] at hhalf; nlinarith
  have hgramsmall : 8*(n : ℝ)^2*(C*δ) ≤ β := by dsimp only [D] at hbet; nlinarith
  have herrorsmall : 4*(n : ℝ)^2*(C*δ) ≤ θ := by
    dsimp only [D] at htheta
    nlinarith [mul_nonneg ha hδ.le]
  refine ⟨δ,hδ,?_⟩
  intro p R hR hcurv u v hfirst t ht htR
  let μ := hausdorff n X
  let U := sobolevColumnMap μ hX.quadratic u
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < τ*R) ht
  have htSub : ball p t ⊆ ball p (2*R) := ball_subset_ball (by linarith)
  have hRSub : ball p t ⊆ ball p R := ball_subset_ball htR
  have hz : μ (ball p t) ≠ 0 := (hX.fullSupport _ _ ht0).ne'
  have hf : μ (ball p t) ≠ ⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hΩz : μ (ball p (2*R)) ≠ 0 := (hX.fullSupport _ _ (by positivity)).ne'
  have hΩf : μ (ball p (2*R)) ≠ ⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
  obtain ⟨hinner,A,hA,hnorm,hdir⟩ := hnormalize p R δ hR hcurv hδ.le hsmall u v hfirst t ht htR
  have houter (z : Euclidean n) : (μ.real (ball p (2*R)))⁻¹*(∫ x in ball p (2*R),
      |localGamma μ hX.quadratic (U (A z)) (U (A z)) x-‖z‖^2| ∂μ)
      ≤ 4*(n : ℝ)^2*(C*δ)*‖z‖^2 := by
    have he := normalized_outer_direction_error μ hX.quadratic u (ball p t) (ball p (2*R))
      measurableSet_ball hz hf hΩz hΩf hδ.le (mul_nonneg (zero_le_one.trans hC) hδ.le)
      hsmall hinner.gram hfirst.gram A hA z
    have hcoef : 2*(n : ℝ)^2*(δ+C*δ) ≤ 4*(n : ℝ)^2*(C*δ) := by
      nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (mul_nonneg (sub_nonneg.mpr hC) hδ.le)]
    exact he.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
  have hg (i : Fin n) : ∀ᵐ x ∂μ.restrict (ball p R),
      localGamma μ hX.quadratic (transformedColumn μ hX.quadratic u A i)
        (transformedColumn μ hX.quadratic u A i) x ≤ 1+β := by
    let ei : Euclidean n := EuclideanSpace.single i 1
    have hAi : ‖A ei‖^2 ≤ 2 := by
      have he : ‖A ei‖ ≤ ‖(A : Euclidean n →L[ℝ] Euclidean n)‖ := by
        simpa only [ei,PiLp.norm_single,norm_one,mul_one,ContinuousLinearEquiv.coe_coe] using
          (A : Euclidean n →L[ℝ] Euclidean n).le_opNorm ei
      exact (pow_le_pow_left₀ (norm_nonneg _) he 2).trans hnorm
    have hcoarse := hfirst.directional_gradient μ hX.quadratic (A ei)
    have hcoef : ((n : ℝ)*(1+δ))^2 ≤ 4*(n : ℝ)^2 :=
      splittingDirectionBound_sq_le hδ.le hδ1
    have hb : ∀ᵐ x ∂μ.restrict (ball p (2*R)),
        localGamma μ hX.quadratic (U (A ei)) (U (A ei)) x ≤ 8*(n : ℝ)^2 := by
      filter_upwards [hcoarse] with x hx
      have hm := mul_le_mul hcoef hAi (sq_nonneg _) (by positivity : 0 ≤ 4*(n : ℝ)^2)
      nlinarith
    have he : (μ.real (ball p (2*R)))⁻¹*(∫ x in ball p (2*R),
        |localGamma μ hX.quadratic (U (A ei)) (U (A ei)) x-1| ∂μ) ≤ θ := by
      have hh := houter ei
      simp only [ei,PiLp.norm_single,norm_one,one_pow,mul_one] at hh
      exact hh.trans herrorsmall
    exact hsharp p R hR hcurv (U (A ei))
      (IsSobolevHarmonicOn.linearCombination μ hX.quadratic hfirst.harmonic (A ei)) hb he
  have hgrams : ∀ i j : Fin n, (μ.real (ball p t))⁻¹*∫ x in ball p t,
      |localGamma μ hX.quadratic (transformedColumn μ hX.quadratic u A i)
        (transformedColumn μ hX.quadratic u A j) x-(if i=j then 1 else 0)| ∂μ ≤ β := by
    have hh := directional_error_implies_gram μ hX.quadratic (transformedColumn μ hX.quadratic u A)
      (ball p t) hf (show 0 ≤ 4*(n : ℝ)^2*(C*δ) by positivity) (by
        intro z
        rw [sobolevColumnMap_transformed]
        exact hdir z)
    intro i j
    exact (hh i j).trans (by nlinarith only [hgramsmall])
  refine ⟨A,⟨?_,?_,?_,?_,hgrams⟩,hA⟩
  · intro i
    have he := sobolevColumnMap_representative μ hX.quadratic u (ball p t) v
      (fun j => ae_restrict_of_ae_restrict_of_subset htSub (hfirst.representative j))
      (A (EuclideanSpace.single i 1))
    filter_upwards [he] with x hx
    change SobolevSpace.toLp μ hX.quadratic (U (A (EuclideanSpace.single i 1))) x = _
    rw [hx]
    have ha := ContinuousLinearMap.adjoint_inner_left
      (A : Euclidean n →L[ℝ] Euclidean n) (EuclideanSpace.single i 1) (v x)
    simpa only [real_inner_comm,EuclideanSpace.inner_single_right,starRingEnd_apply,
      star_trivial,one_mul,ContinuousLinearEquiv.coe_coe] using ha.symm
  · exact (A : Euclidean n →L[ℝ] Euclidean n).adjoint.continuous.comp_continuousOn
      (hfirst.continuous.mono htSub)
  · exact transformedColumn_harmonic μ hX.quadratic u A (ball p t)
      (fun i => (hfirst.harmonic i).mono μ hX.quadratic htSub)
  · intro i
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hRSub (hg i)] with x hx
    exact hx.trans (by nlinarith : 1+β ≤ (1+β)^2)

theorem NoncollapsedRCD.comparable_radius_splitting {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (β : ℝ) (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : X) (R : ℝ), 0 < R → -1 ≤ K*(2*R)^2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) δ u v →
      ∀ t : ℝ, R/2 ≤ t → t ≤ R → ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p t β
          (transformedColumn (hausdorff n X) hX.quadratic u A)
          (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
        IsExactMeanNormalization (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u) (ball p t) measurableSet_ball A := by
  simpa only [show ∀ R : ℝ, (1/2)*R=R/2 by intro R; ring] using
    hX.interior_radius_splitting hn (1/2) (by norm_num) (by norm_num) β hβ

end RegularPointCoordinates

end

end OAI

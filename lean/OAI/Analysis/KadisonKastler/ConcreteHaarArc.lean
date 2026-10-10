import OAI.Analysis.KadisonKastler.TraceProjectionLimits
import OAI.Analysis.KadisonKastler.UnitaryFunctionalCalculus
import OAI.Analysis.KadisonKastler.HaarArc

namespace OAI

/-! # Construction of the spectral arc projection

Continuous circle cutoffs converge in the faithful tracial two-norm.
Bounded completeness realizes their limit as a projection in the given
von Neumann algebra, with its exact Haar mass and commutation relation.
-/

namespace KadisonKastler

open Filter MeasureTheory
open scoped Topology

noncomputable section

local instance haarArcPositivePeriod : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The actual projection obtained from the continuous arc cutoffs. -/
structure HaarArcProjection (τ : FaithfulTracialState (Algebra M))
    (u : unitary (Algebra M)) (a : ℝ) where
  projection : Algebra M
  isStarProjection : IsStarProjection projection
  norm_le : ‖projection‖ ≤ 1
  strong_limit : ∀ ξ, Tendsto
    (fun n => (unitaryCircleCFC u (haarArcCutoff a n) : H →L[ℂ] H) ξ) atTop
      (𝓝 ((projection : H →L[ℂ] H) ξ))
  two_limit : Tendsto
    (fun n => traceTwoNorm τ (unitaryCircleCFC u (haarArcCutoff a n) - projection)) atTop (𝓝 0)

/-- The spectral arc projection is constructed, rather than assumed. -/
theorem nonempty_haarArcProjection (τ : FaithfulTracialState (Algebra M))
    (hτ : FiniteVectorTrace τ) (u : unitary (Algebra M))
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower u k) = 0) (a : ℝ) :
    Nonempty (HaarArcProjection τ u a) := by
  let x (n : ℕ) := unitaryCircleCFC u (haarArcCutoff a n)
  have hx (n : ℕ) : ‖x n‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le (unitaryCircleCFC u) _).trans
      (norm_haarArcCutoff_le_one a n)
  have hs (n : ℕ) : IsSelfAdjoint (x n) := by
    show star (x n) = x n
    change star (unitaryCircleCFC u (haarArcCutoff a n)) = _
    rw [← map_star, star_haarArcCutoff]
  obtain ⟨e, he, hn, hstrong, htwo⟩ := hτ.projection_limit x hx hs
    (haarArcCutoff_traceTwoNorm_cauchy τ u hhaar (unitaryCircleCFC u)
      (unitaryCircleCFC_fourier u) a)
    (tendsto_traceTwoNorm_haarArcCutoff_idempotency τ u hhaar (unitaryCircleCFC u)
      (unitaryCircleCFC_fourier u) a)
  exact ⟨⟨e, he, hn, hstrong, htwo⟩⟩

/-- The arc projection commutes with the unitary whose spectrum defines it. -/
theorem HaarArcProjection.commute {τ : FaithfulTracialState (Algebra M)}
    {u : unitary (Algebra M)} {a : ℝ} (E : HaarArcProjection τ u a) :
    Commute (u : Algebra M) E.projection := by
  have hc (n : ℕ) : (u : Algebra M) * unitaryCircleCFC u (haarArcCutoff a n) =
      unitaryCircleCFC u (haarArcCutoff a n) * (u : Algebra M) := by
    calc
      _ = unitaryCircleCFC u (fourier 1) * unitaryCircleCFC u (haarArcCutoff a n) := by
        rw [unitaryCircleCFC_fourier_one]
      _ = unitaryCircleCFC u (haarArcCutoff a n) * unitaryCircleCFC u (fourier 1) := by
        exact (map_mul _ _ _).symm.trans
          ((congrArg (unitaryCircleCFC u) (mul_comm (fourier 1) (haarArcCutoff a n))).trans
            (map_mul _ _ _))
      _ = _ := by rw [unitaryCircleCFC_fourier_one]
  change (u : Algebra M) * E.projection = E.projection * (u : Algebra M)
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro ξ
  have hL := ((u : H →L[ℂ] H).continuous.tendsto _).comp (E.strong_limit ξ)
  have hR := E.strong_limit ((u : H →L[ℂ] H) ξ)
  have heq (n : ℕ) : (u : H →L[ℂ] H)
      ((unitaryCircleCFC u (haarArcCutoff a n) : H →L[ℂ] H) ξ) =
      (unitaryCircleCFC u (haarArcCutoff a n) : H →L[ℂ] H) ((u : H →L[ℂ] H) ξ) := by
    exact congrArg (fun b : Algebra M => (b : H →L[ℂ] H) ξ) (hc n)
  have h := tendsto_nhds_unique (hL.congr' (Eventually.of_forall heq)) hR
  exact h

/-- The constructed projection has the normalized angular Haar mass. -/
theorem HaarArcProjection.trace {τ : FaithfulTracialState (Algebra M)}
    {u : unitary (Algebra M)} {a : ℝ} (E : HaarArcProjection τ u a)
    (hτ : FiniteVectorTrace τ)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower u k) = 0)
    (ha : 0 ≤ a) (hapi : a ≤ Real.pi) :
    τ.toLinearMap E.projection = ((a / Real.pi : ℝ) : ℂ) := by
  have htrace := hτ.tendsto (fun n => unitaryCircleCFC u (haarArcCutoff a n)) E.projection
    (fun ξ η => tendsto_const_nhds.inner (E.strong_limit ξ))
  have hscalar := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_integral_haarArcCutoffReal ha hapi)
  have heq (n : ℕ) : τ.toLinearMap (unitaryCircleCFC u (haarArcCutoff a n)) =
      ((∫ t, haarArcCutoffReal a n t ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)) : ℝ) : ℂ) := by
    rw [trace_unitaryCircleCFC τ u hhaar, haarCircleIntegral_apply]
    exact integral_complex_ofReal
  apply tendsto_nhds_unique htrace
  simpa only [heq, Function.comp_def] using hscalar

/-- The normalized scalar Fourier polynomial maps to the actual polynomial. -/
theorem unitaryCircleCFC_haarCirclePolynomial (u : unitary (Algebra M)) (N : ℕ) :
    unitaryCircleCFC u (haarCirclePolynomial N) = unitaryHaarPolynomial N u := by
  rw [unitaryHaarPolynomial_eq_real_smul]
  simp only [haarCirclePolynomial, ← Complex.coe_smul, map_smul, map_sum, unitaryCircleCFC_fourier,
    haarPower_natCast, unitaryHaarSum]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun r => (u : Algebra M) ^ (r + 1)) N).symm

/-- Every polynomial in the unitary commutes with its arc projection. -/
theorem HaarArcProjection.polynomial_commute {τ : FaithfulTracialState (Algebra M)}
    {u : unitary (Algebra M)} {a : ℝ} (E : HaarArcProjection τ u a) (N : ℕ) :
    Commute (unitaryHaarPolynomial N u) E.projection := by
  unfold unitaryHaarPolynomial unitaryHaarSum
  apply Commute.smul_left
  apply Commute.sum_left
  intro r hr
  exact E.commute.pow_left _

/-- The constructed operator projection has exactly the scalar Haar tail
energy for every normalized Fourier polynomial. -/
theorem HaarArcProjection.tail {τ : FaithfulTracialState (Algebra M)}
    {u : unitary (Algebra M)} {a : ℝ} (E : HaarArcProjection τ u a)
    (hτ : FiniteVectorTrace τ)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower u k) = 0)
    (ha : 0 ≤ a) (hapi : a ≤ Real.pi) (N : ℕ) :
    (τ.toLinearMap (star (unitaryHaarPolynomial N u) * unitaryHaarPolynomial N u *
      (1 - E.projection))).re = haarTailEnergy N a := by
  let f := unitaryHaarPolynomial N u
  let b := star f * f
  let x (n : ℕ) := unitaryCircleCFC u (haarArcCutoff a n)
  have hstrong (ξ : H) : Tendsto
      (fun n => ((b * (1 - x n) : Algebra M) : H →L[ℂ] H) ξ) atTop
      (𝓝 (((b * (1 - E.projection) : Algebra M) : H →L[ℂ] H) ξ)) := by
    have hsub := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ξ) atTop (𝓝 ξ)).sub
      (E.strong_limit ξ)
    exact ((b : H →L[ℂ] H).continuous.tendsto _).comp hsub
  have ht := hτ.tendsto (fun n => b * (1 - x n)) (b * (1 - E.projection))
    (fun ξ η => tendsto_const_nhds.inner (hstrong ξ))
  have heq (n : ℕ) : τ.toLinearMap (b * (1 - x n)) =
      ((∫ t, ‖haarCirclePolynomial N t‖ ^ 2 * (1 - haarArcCutoffReal a n t)
        ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)) : ℝ) : ℂ) := by
    have halg : b * (1 - x n) = unitaryCircleCFC u
        (star (haarCirclePolynomial N) * haarCirclePolynomial N * (1 - haarArcCutoff a n)) := by
      simp only [map_mul, map_sub, map_star, map_one, unitaryCircleCFC_haarCirclePolynomial,
        b, f, x]
    rw [halg, trace_unitaryCircleCFC τ u hhaar, haarCircleIntegral_apply]
    calc
      _ = ∫ t, ((‖haarCirclePolynomial N t‖ ^ 2 * (1 - haarArcCutoffReal a n t) : ℝ) : ℂ)
          ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        change star (haarCirclePolynomial N t) * haarCirclePolynomial N t *
          (1 - (haarArcCutoffReal a n t : ℂ)) = _
        rw [Complex.star_def, Complex.conj_mul']
        norm_cast
      _ = _ := integral_complex_ofReal
  have hr := (Complex.continuous_re.tendsto _).comp ht
  have hscalar := tendsto_integral_haarCirclePolynomial_cutoff_compl ha hapi N
  have hh : Tendsto (fun n => (τ.toLinearMap (b * (1 - x n))).re) atTop
      (𝓝 (haarTailEnergy N a)) := by
    simpa only [heq, Complex.ofReal_re] using hscalar
  exact tendsto_nhds_unique hr hh

end

end KadisonKastler

end OAI

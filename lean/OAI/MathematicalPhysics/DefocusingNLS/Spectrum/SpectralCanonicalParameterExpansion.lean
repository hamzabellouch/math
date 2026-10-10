import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalParameterEquation
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingBounds

namespace OAI

/-! Parameter derivatives of a canonical column have arbitrarily accurate
finite expansions with a bounded weighted remainder. -/

open Filter Topology Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_circular_local_formula (ν η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ) (J : ℕ) :
    ∃ j : ℕ, J ≤ j ∧ ∃ hκ : 0 < 2 * (j : ℝ), ∃ q : ℝ →ᵇ ℂ,
      ∃ f : ℂ → CircularTailSpace,
        (∀ w, AnalyticAt ℂ f w) ∧
        circularFieldBound (ν - 2 * z) (star ν - 2 * z) η n ‖q‖ < 2 * (j : ℝ) ∧
        ∀ lam, circularFieldBound (ν - 2 * lam) (star ν - 2 * lam) η n ‖q‖ < 2 * (j : ℝ) →
          ∀ t, 0 ≤ t → Y lam t =
            circularPolynomialJet (spectralOutgoingPolynomial (ν - 2 * lam) (star ν - 2 * lam)
              η n (radialExteriorExpansion ν n b j) c j) t +
            circularUnweight (2 * (j : ℝ))
              (circularResolvedCorrection (2 * (j : ℝ)) hκ ν (star ν) η n hn q f lam) t := by
  obtain ⟨q, hq, hP⟩ := canonical_circular_expansion_data ν b n L hX hb
  let C := circularFieldBound (ν - 2 * z) (star ν - 2 * z) η n ‖q‖
  have hC : 0 ≤ C := circularFieldBound_nonneg _ _ _ _ _
  obtain ⟨N, hN⟩ := exists_nat_gt (C + 1)
  obtain ⟨j, hmaxj, e, he⟩ := hP (max J N)
  have hNj : N ≤ j := (le_max_right J N).trans hmaxj
  have hNj' : (N : ℝ) ≤ j := by exact_mod_cast hNj
  have hgap : C < 2 * (j : ℝ) := by linarith
  let κ : ℝ := 2 * (j : ℝ)
  have hκ : 0 < κ := lt_of_le_of_lt hC hgap
  let P := radialExteriorExpansion ν n b j
  obtain ⟨A, B, hAB⟩ := exists_bounded_normalized_coefficients n κ q (boundedRadialPolynomial P) e (by
    intro t ht
    simpa only [boundedRadialPolynomial_nonneg P t ht] using he t ht)
  let f := spectralAnalyticTailData ν (star ν) η n P c j A B
  let v := circularResolvedCorrection κ hκ ν (star ν) η n hn q f
  let U := fun lam => spectralOutgoingPolynomial (ν - 2 * lam) (star ν - 2 * lam) η n P c j
  let W := fun lam t => circularPolynomialJet (U lam) t + circularUnweight κ (v lam) t
  have hWd (lam : ℂ)
      (hlam : circularFieldBound (ν - 2 * lam) (star ν - 2 * lam) η n ‖q‖ < κ)
      (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (W lam) (circularLeadingField t (W lam t) +
        circularBoundedField (ν - 2 * lam) (star ν - 2 * lam) η n (q t) (W lam t)) t := by
    apply circularPolynomial_corrected (ν - 2 * lam) (star ν - 2 * lam) η n P (U lam)
      (circularUnweight κ (v lam)) (q t) t
    have hd := circularResolvedCorrection_hasDerivAt κ hκ ν (star ν) η n hn q f lam hlam t
    have hu := circularUnweight_hasDerivAt κ t (ν - 2 * lam) (star ν - 2 * lam) η n (q t)
      (v lam) (circularTailEvaluation (f lam) t) hd
    have hf := spectralAnalyticTailData_normalized ν (star ν) η n P c j A B q hAB lam t ht
    change Real.exp (-κ * t) • circularTailEvaluation (f lam) t = _ at hf
    simpa only [hf, add_sub_assoc] using hu
  refine ⟨j, (le_max_left J N).trans hmaxj, hκ, q, f, ?_, hgap, ?_⟩
  · intro w
    exact spectralAnalyticTailData_analyticAt ν (star ν) η n P c j A B w
  · intro lam hlam t ht
    obtain ⟨k, hjk, w, hw⟩ := hY.2.2.2 lam j
    have heq := circular_outgoing_orders_unique ν (ν - 2 * lam) (star ν - 2 * lam)
      η b n hn c j k hjk (v lam) w ‖q‖ 0 q (W lam) (Y lam)
      (fun s _ => q.norm_coe_le_norm s) (hWd lam hlam)
      (fun s hs => by simpa only [hq s hs] using hY.1 lam s hs)
      (fun _ _ => rfl) hw hlam
    exact (heq t (by simpa only [max_self] using ht)).symm

theorem canonical_circular_parameter_expansion (ν η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ) (J : ℕ) :
    ∃ j : ℕ, J ≤ j ∧ ∃ U : ℂ[X] × ℂ[X], ∃ v : CircularTailSpace,
      ∀ t, 0 ≤ t → deriv (fun lam => Y lam t) z =
        circularPolynomialJet U t + circularUnweight (2 * (j : ℝ)) v t := by
  obtain ⟨j, hJj, hκ, q, f, hf, hgap, heq⟩ :=
    canonical_circular_local_formula ν η b n hn L hX hb c Y hY z J
  let P := radialExteriorExpansion ν n b j
  let U := fun lam => spectralOutgoingPolynomial (ν - 2 * lam) (star ν - 2 * lam) η n P c j
  let v := circularResolvedCorrection (2 * (j : ℝ)) hκ ν (star ν) η n hn q f
  have hcoef (k : ℕ) := spectralOutgoingPolynomial_coeff_analytic
    (fun lam => ν - 2 * lam) (fun lam => star ν - 2 * lam) η n P c z
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) j k
  have hdeg (lam : ℂ) := spectralOutgoingPolynomial_degree
    (ν - 2 * lam) (star ν - 2 * lam) η n P c j
  refine ⟨j, hJj, (polynomialParameterDerivative (fun lam => (U lam).1) j z,
    polynomialParameterDerivative (fun lam => (U lam).2) j z), deriv v z, ?_⟩
  intro t ht
  have hnear : ∀ᶠ lam in 𝓝 z,
      circularFieldBound (ν - 2 * lam) (star ν - 2 * lam) η n ‖q‖ < 2 * (j : ℝ) := by
    have hc : Continuous (fun lam : ℂ =>
        circularFieldBound (ν - 2 * lam) (star ν - 2 * lam) η n ‖q‖) := by
      unfold circularFieldBound
      fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds hgap)
  have he : (fun lam => Y lam t) =ᶠ[𝓝 z]
      (fun lam => circularPolynomialJet (U lam) t + circularUnweight (2 * (j : ℝ)) (v lam) t) := by
    filter_upwards [hnear] with lam hlam
    exact heq lam hlam t ht
  rw [he.deriv_eq]
  exact ((circularPolynomialJet_hasParameterDerivAt (fun lam => (U lam).1)
    (fun lam => (U lam).2) j z (fun lam => (hdeg lam).1) (fun lam => (hdeg lam).2)
    (fun k => (hcoef k).1) (fun k => (hcoef k).2) t).add
    (circularUnweight_hasParameterDerivAt (2 * (j : ℝ)) t v (deriv v z) z
      (circularResolvedCorrection_analyticAt (2 * (j : ℝ)) hκ ν (star ν) η n hn q f z
        (hf z) hgap).differentiableAt.hasDerivAt)).deriv

theorem canonical_circular_parameter_bounded (ν η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ) :
    ∃ C : ℝ, ∀ t, 0 ≤ t → ‖deriv (fun lam => Y lam t) z‖ ≤ C := by
  obtain ⟨j, _, U, v, he⟩ := canonical_circular_parameter_expansion ν η b n hn L hX hb c Y hY z 0
  exact ⟨‖boundedCircularPolynomialJet U‖ + ‖v‖,
    fun t ht => circular_expansion_bound U j v (fun s => deriv (fun lam => Y lam s) z) he t ht⟩

end DefocusingNLS

end OAI

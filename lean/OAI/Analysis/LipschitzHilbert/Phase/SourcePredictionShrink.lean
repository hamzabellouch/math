import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionMotion
import OAI.Analysis.LipschitzHilbert.Estimates.RadialShrink

namespace OAI

/-! The source snapshot shrinkage gives the one-sided denominator
comparison and preserves numerator motion with its child-mass factor. -/

noncomputable section
namespace LipschitzHilbert

theorem prediction_mass_scale_factor {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (p μ : ℝ) :
    massPowerScale n c (-(1/p)) (μ-1+1/p) = (c/n)^(1/p)*c^(μ-1) := by
  rw [massPowerScale, Real.rpow_neg hn.le, Real.div_rpow hc.le hn.le,
    Real.rpow_add hc]
  ring

section RealVector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Apply the source shrinkage to the original amplitude, before mass
normalization. The resulting model denominator is below every moved one. -/
theorem source_prediction_denominator_shrink {n n' c c' p μ ε : ℝ}
    (hn : 0 < n) (hn' : 0 < n') (hc : 0 < c) (hc' : 0 < c')
    (hp : 0 < p) (hε : 0 ≤ ε) (U : E →ₗᵢ[ℝ] E) (A A' : E)
    (hmotion : ‖massPowerScale n' c' (-(1/p)) (μ-1+1/p) • A'-
        U (massPowerScale n c (-(1/p)) (μ-1+1/p) • A)‖ ≤
      ε*(c/n)^(1/p)*c^μ) :
    (c/n)*‖c^(μ-1) • radialShrink (2*ε*c) A‖^p ≤
      (c'/n')*‖c'^(μ-1) • A'‖^p := by
  let s := massPowerScale n c (-(1/p)) (μ-1+1/p)
  let s' := massPowerScale n' c' (-(1/p)) (μ-1+1/p)
  have hs : 0 ≤ s := (massPowerScale_pos hn hc _ _).le
  have hmotion' : ‖s' • A'-U (s • A)‖ ≤ s*(2*ε*c) := by
    apply hmotion.trans
    have heq := prediction_mass_scale_identity hn hc p μ
    have heq' : ε*(c/n)^(1/p)*c^μ = s*(ε*c) := by
      calc
        _ = ε*((c/n)^(1/p)*c^μ) := by ring
        _ = ε*(s*c) := by rw [← heq]
        _ = _ := by ring
    rw [heq']
    exact mul_le_mul_of_nonneg_left (by nlinarith) hs
  have hnorm : ‖U (s • A)‖ = s*‖A‖ := by
    rw [U.norm_map, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
  have hb := scaled_radialShrink_power_le_of_error
    (show 0 ≤ 2*ε*c by positivity) hs hp.le A (s' • A') (U (s • A)) hnorm hmotion'
  have hleft : s • radialShrink (2*ε*c) A =
      (c/n)^(1/p) • (c^(μ-1) • radialShrink (2*ε*c) A) := by
    rw [← mul_smul]
    exact congrArg (fun r : ℝ => r • radialShrink (2*ε*c) A)
      (prediction_mass_scale_factor hn hc p μ)
  have hright : s' • A' = (c'/n')^(1/p) • (c'^(μ-1) • A') := by
    rw [← mul_smul]
    exact congrArg (fun r : ℝ => r • A') (prediction_mass_scale_factor hn' hc' p μ)
  rw [hleft,hright,norm_weighted_smul_rpow hp (div_pos hc hn).le,
    norm_weighted_smul_rpow hp (div_pos hc' hn').le] at hb
  exact hb

theorem source_prediction_shrink_zero {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (A : E) (hA : ‖A‖ ≤ ε*c) : radialShrink (2*ε*c) A = 0 := by
  apply (radialShrink_eq_zero_iff (by positivity) A).mpr
  exact hA.trans (by nlinarith)

end RealVector

section ComplexVector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Shrinking the snapshot costs another two copies of the same
relative-child-mass error. The common diagonal carrier stays explicit. -/
theorem source_prediction_shrunk_numerator {n c μ ε K : ℝ}
    (hn : 0 < n) (hc : 0 ≤ c) (hε : 0 ≤ ε) (hK : n^μ ≤ K)
    (U : E →ₗᵢ[ℂ] E) (A actual : E) (lam : ℂ) (hlam : ‖lam‖ ≤ 1)
    (hmotion : ‖actual-((n^(μ-1):ℝ):ℂ) • (lam • U A)‖ ≤ ε*K*(c/n)) :
    ‖actual-((n^(μ-1):ℝ):ℂ) •
      (lam • U (radialShrink (2*ε*c) A))‖ ≤ (3*ε*K)*(c/n) := by
  have hscalar : 0 ≤ n^(μ-1) := Real.rpow_nonneg hn.le _
  have hshrink : ‖A-radialShrink (2*ε*c) A‖ ≤ 2*ε*c := by
    rw [norm_sub_rev]
    exact norm_radialShrink_sub_le (by positivity) A
  have herror : ‖((n^(μ-1):ℝ):ℂ) • (lam • U A)-
      ((n^(μ-1):ℝ):ℂ) • (lam • U (radialShrink (2*ε*c) A))‖ ≤
      2*ε*K*(c/n) := by
    rw [← smul_sub, ← smul_sub, ← map_sub, norm_smul, norm_smul, U.norm_map,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscalar]
    calc
      _ ≤ n^(μ-1)*(1*(2*ε*c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hlam hshrink (norm_nonneg _) zero_le_one) hscalar
      _ = (2*ε)*(n^μ*(c/n)) := by
        rw [← prediction_numerator_scale_identity hn]
        ring
      _ ≤ (2*ε)*(K*(c/n)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hK (div_nonneg hc hn.le)) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ‖actual-((n^(μ-1):ℝ):ℂ) • (lam • U A)‖+
        ‖((n^(μ-1):ℝ):ℂ) • (lam • U A)-
          ((n^(μ-1):ℝ):ℂ) • (lam • U (radialShrink (2*ε*c) A))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε*K*(c/n)+2*ε*K*(c/n) := add_le_add hmotion herror
    _ = _ := by ring

end ComplexVector
end LipschitzHilbert

end

end OAI

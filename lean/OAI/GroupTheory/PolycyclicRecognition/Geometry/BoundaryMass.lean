import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarAveraging
import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryHeight

namespace OAI

/-!
# Boundary masses determine trace height

This specializes the proved Haar averaging lemma to the exponential volume
characters of the ray quotients. The conclusion is the uniformly bounded
trace-height error, with the reference value subtracted.
-/

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure

theorem trace_bound_of_boundary_masses
    {G J : Type*} [Group G] [MeasurableSpace G] [MetricSpace G]
    [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] [IsIsometricSMul G G]
    (μ ρ : Measure G) [SFinite μ] [SFinite ρ]
    [IsInvInvariant μ] [IsMulRightInvariant μ]
    (E : J → Set G) (source target : J → ℝ)
    (hE : ∀ j, IsCompact (E j))
    {c K D : ℝ} (hc : 0 < c) (hK : 0 < K) (hD : 0 < D)
    (hvolume : ∀ j, μ (E j) = ENNReal.ofReal (c * Real.exp (source j)))
    (hlower : ∀ j z, ENNReal.ofReal (Real.exp (target j)) ≤
      ENNReal.ofReal K * ρ (leftTranslate (E j) z))
    (hupper : ∀ j z, ρ (leftTranslate (E j) z) ≤
      ENNReal.ofReal K * ENNReal.ofReal (Real.exp (target j)))
    (hballs : ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T, T₀ ≤ T →
      μ (Metric.ball 1 T) ≠ 0 ∧ μ (Metric.ball 1 T) ≠ ⊤ ∧
      μ (Metric.ball 1 (2 * T)) ≤ ENNReal.ofReal D * μ (Metric.ball 1 T)) :
    ∀ j j₀, |(target j - target j₀) - (source j - source j₀)| ≤
      Real.log (K * K * (D * D)) := by
  have hcmp := haar_averaging_compact μ ρ E
    (fun j => ENNReal.ofReal (Real.exp (target j))) hE ENNReal.ofReal_ne_top
    hlower hupper hballs
  have hreal (j k : J) :
      Real.exp (target j) * Real.exp (source k) ≤
        (K * K * (D * D)) * (Real.exp (target k) * Real.exp (source j)) := by
    have h := hcmp j k
    rw [hvolume j, hvolume k] at h
    have h' := ENNReal.toReal_mono (by finiteness) h
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal hK.le, ENNReal.toReal_ofReal hD.le,
      ENNReal.toReal_ofReal (mul_pos hc (Real.exp_pos _)).le] at h'
    apply (mul_le_mul_iff_right₀ hc).mp
    convert h' using 1 <;> ring
  intro j j₀
  have h := abs_log_sub_le_of_comparison
    (mul_pos (Real.exp_pos (target j)) (Real.exp_pos (source j₀)))
    (mul_pos (Real.exp_pos (target j₀)) (Real.exp_pos (source j)))
    (by positivity : 0 < K * K * (D * D)) (hreal j j₀) (hreal j₀ j)
  simp only [Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp] at h
  convert h using 1
  congr 1
  ring

end PolycyclicRecognition

end OAI

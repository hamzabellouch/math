import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! # Vanishing square integrals imply vanishing L1 integrals on finite measures -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.CollisionCompactness

theorem integral_abs_tendsto_zero_of_square {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : ℕ → X → ℝ}
    (hi : ∀ n, Integrable (f n) μ)
    (hi2 : ∀ n, Integrable (fun x => (f n x)^2) μ)
    (ht : Tendsto (fun n => ∫ x, (f n x)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, |f n x| ∂μ) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let M := μ.real Set.univ
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  let δ := ε/(2*(M+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : δ*M < ε/2 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(M+1))).mpr
    nlinarith
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (δ*ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hlim : (∫ x, (f n x)^2 ∂μ) < δ*ε/2 := by
    have h := hN n hn
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun x => sq_nonneg _))] at h
    exact h
  have hb : (∫ x, |f n x| ∂μ) ≤ δ*M+(∫ x, (f n x)^2 ∂μ)/δ := by
    calc
      _ ≤ ∫ x, δ+(f n x)^2/δ ∂μ := by
        apply integral_mono (hi n).abs ((integrable_const δ).add ((hi2 n).div_const δ))
        intro x
        change |f n x| ≤ δ+(f n x)^2/δ
        have hs := sq_nonneg (|f n x|-δ)
        have hs' : |f n x| * δ ≤ δ^2+(f n x)^2 := by nlinarith [sq_abs (f n x)]
        calc
          _ ≤ (δ^2+(f n x)^2)/δ := (le_div_iff₀ hδ).mpr hs'
          _ = _ := by field_simp
      _ = _ := by rw [integral_add (integrable_const δ) ((hi2 n).div_const δ),
        integral_const,smul_eq_mul,integral_div]; dsimp [M]; ring
  have hsmall2 : (∫ x, (f n x)^2 ∂μ)/δ < ε/2 := by
    apply (div_lt_iff₀ hδ).mpr
    nlinarith
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun x => abs_nonneg _))]
  linarith

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI

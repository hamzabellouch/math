import OAI.Probability.InvariantIsing.Fields.PhysicalFieldComparison
import OAI.Probability.InvariantIsing.Cavity.CavityMultiplicityTransport

namespace OAI

/-! Continuity of physical mean pressure under matching limiting finite
spectral and field populations. Zero limiting field weights are allowed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem physical_mean_field_populations_tendsto {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ j, 0<N j)
    (μ : (j : ℕ) → Measure (Orthogonal (N j))) [∀ j, IsProbabilityMeasure (μ j)]
    [∀ j, (μ j).IsMulRightInvariant] (eig : (j : ℕ) → Fin (N j) → ℝ)
    (g h : (j : ℕ) → Fin (N j) → A) (γ b : A → ℝ)
    (hg : Tendsto (fun j a => (spinGroupSize (g j) a : ℝ)/N j) atTop (𝓝 γ))
    (hh : Tendsto (fun j a => (spinGroupSize (h j) a : ℝ)/N j) atTop (𝓝 γ))
    {B : ℝ} (hB : 0≤B) (hb : ∀ a, |b a|≤B) :
    Tendsto (fun j => (∫ U, rotatedPressure (eig j) (matrixRotation U⁻¹) (fun i => b (g j i)) ∂μ j)-
      ∫ U, rotatedPressure (eig j) (matrixRotation U⁻¹) (fun i => b (h j i)) ∂μ j)
      atTop (𝓝 0) := by
  have he a : Tendsto (fun j => |(spinGroupSize (g j) a : ℝ)/N j-
      (spinGroupSize (h j) a : ℝ)/N j|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero] using
      (((tendsto_pi_nhds.mp hg) a).sub ((tendsto_pi_nhds.mp hh) a)).abs
  have hs := (tendsto_finsetSum Finset.univ (fun a _ => he a)).const_mul (2*B)
  simp only [Finset.sum_const_zero,mul_zero] at hs
  apply squeeze_zero_norm (fun j => ?_) hs
  simpa only [Real.norm_eq_abs] using physical_mean_field_counts_le (hN j) (μ j)
    (eig j) (g j) (h j) b hB hb

theorem physical_mean_joint_populations_tendsto {m : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ j, 0<N j)
    (μ : (j : ℕ) → Measure (Orthogonal (N j))) [∀ j, IsProbabilityMeasure (μ j)]
    [∀ j, (μ j).IsMulRightInvariant]
    (e f : (j : ℕ) → Fin (N j) → Fin m) (ρ : Fin m → ℝ) (hρ : ∀ a, 0<ρ a)
    (he : Tendsto (fun j a => (spinGroupSize (e j) a : ℝ)/N j) atTop (𝓝 ρ))
    (hf : Tendsto (fun j a => (spinGroupSize (f j) a : ℝ)/N j) atTop (𝓝 ρ))
    (lam : Fin m → ℝ) {K : ℝ} (hK : 0≤K) (hlam : ∀ a, |lam a|≤K)
    (g h : (j : ℕ) → Fin (N j) → A) (γ b : A → ℝ)
    (hg : Tendsto (fun j a => (spinGroupSize (g j) a : ℝ)/N j) atTop (𝓝 γ))
    (hh : Tendsto (fun j a => (spinGroupSize (h j) a : ℝ)/N j) atTop (𝓝 γ))
    {B : ℝ} (hB : 0≤B) (hb : ∀ a, |b a|≤B) :
    Tendsto (fun j => (∫ U, rotatedPressure (fun i => lam (f j i)) (matrixRotation U⁻¹)
      (fun i => b (h j i)) ∂μ j)-
      ∫ U, rotatedPressure (fun i => lam (e j i)) (matrixRotation U⁻¹)
      (fun i => b (g j i)) ∂μ j) atTop (𝓝 0) := by
  have hs := cavity_meanPressure_same_proportions_tendsto N hN μ e f ρ hρ he hf lam
    (fun j i => b (h j i)) K hlam (2*K) (by positivity)
    (fun a b => (abs_sub _ _).trans (by linarith [hlam a,hlam b]))
  have ht := physical_mean_field_populations_tendsto N hN μ (fun j i => lam (e j i))
    h g γ b hh hg hB hb
  have hz := hs.add ht
  simp only [add_zero] at hz
  convert hz using 1
  funext j
  ring

end InvariantIsing

end

end OAI

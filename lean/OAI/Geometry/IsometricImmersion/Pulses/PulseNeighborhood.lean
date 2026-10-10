import OAI.Geometry.IsometricImmersion.Assembly.SupportedNeighborhoods
import OAI.Geometry.IsometricImmersion.Pulses.PulseDerivativeBounds

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem pulse_support_eventually (q0 a delta : ℝ) (hq : |q0| * a < 1 / 10) :
    ∀ᶠ tau : ℝ in atTop, delta / (2 * tau) + |q0| * a < 1 / 10 := by
  have h : Tendsto (fun tau : ℝ => delta / (2 * tau) + |q0| * a)
      atTop (𝓝 (|q0| * a)) := by
    have hi := (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0))
    simpa [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using
      (hi.const_mul (delta / 2)).add_const (|q0| * a)
  exact h.eventually_lt tendsto_const_nhds hq

theorem pulse_finite_derivative_bounds_eventually (q0 a : ℝ) (ha : 0 < a)
    (delta : ℝ) (N : ℕ) {epsilon : ℝ} (heps : 0 < epsilon) :
    ∀ᶠ tau : ℝ in atTop, ∀ k ∈ Finset.range N,
      pulseDerivativeBound q0 a ha delta k * tau ^ k / tau ^ N < epsilon := by
  apply (Finset.range N).eventually_all.mpr
  intro k hk
  exact (fixed_order_pulse_bound_tendsto_zero q0 a ha delta N k (Finset.mem_range.mp hk)).eventually_lt
    tendsto_const_nhds heps

theorem perturbedMetric_add_supportedPulse (g0 : MetricField) (η : SymmetricPerturbation)
    (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau)
    (hax : a ≤ 1 / 10) (hay : delta / (2 * tau) + |q0| * a ≤ 1 / 10) :
    perturbedMetric g0 (η + supportedPulse q0 a N delta tau ha hd ht hax hay) =
      testMetric (perturbedMetric g0 η) q0 a N delta tau := by
  ext p i j
  change g0 p i j + (perturbationTensor η p i j + pulseTensor q0 a N delta tau p i j) =
    (g0 p i j + perturbationTensor η p i j) + pulseTensor q0 a N delta tau p i j
  ring

theorem exists_N_before_delta_eventually_mem {O : Set SymmetricPerturbation}
    (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |q0| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℝ in atTop, 1 ≤ tau ∧
        ∃ ρ : SymmetricPerturbation,
          perturbationTensor ρ = pulseTensor q0 a N delta tau ∧ η + ρ ∈ O := by
  obtain ⟨N, epsilon, hN, heps, hball⟩ := exists_ordered_seminorm_neighborhood hO hη
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [eventually_ge_atTop (1 : ℝ), pulse_support_eventually q0 a delta hq,
    pulse_finite_derivative_bounds_eventually q0 a ha delta N heps] with tau ht hshape hsmall
  let ρ : SymmetricPerturbation :=
    supportedPulse q0 a N delta tau ha hd (lt_of_lt_of_le zero_lt_one ht) hax hshape.le
  refine ⟨ht, ρ, rfl, hball ρ ?_⟩
  intro k hk
  exact (supportedPulse_seminorm_le q0 a ha N delta hd ht hax hshape.le k).trans_lt
    (hsmall k (Finset.mem_range.mpr hk))

theorem exists_N_before_delta_eventually_testMetric (g0 : MetricField)
    {O : Set SymmetricPerturbation} (hO : IsOpen O) {η : SymmetricPerturbation} (hη : η ∈ O)
    (q0 a : ℝ) (ha : 0 < a) (hax : a ≤ 1 / 10) (hq : |q0| * a < 1 / 10) :
    ∃ N : ℕ, 10 < N ∧ ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℝ in atTop, 1 ≤ tau ∧
        ∃ θ ∈ O, perturbedMetric g0 θ = testMetric (perturbedMetric g0 η) q0 a N delta tau := by
  obtain ⟨N, hN, hmem⟩ := exists_N_before_delta_eventually_mem hO hη q0 a ha hax hq
  refine ⟨N, hN, ?_⟩
  intro delta hd
  filter_upwards [hmem delta hd] with tau ht
  obtain ⟨ρ, hρ, hOρ⟩ := ht.2
  refine ⟨ht.1, η + ρ, hOρ, ?_⟩
  ext p i j
  change g0 p i j + (perturbationTensor η p i j + perturbationTensor ρ p i j) =
    (g0 p i j + perturbationTensor η p i j) + pulseTensor q0 a N delta tau p i j
  rw [hρ]
  ring

end SmoothLocal.Pulse

end

end OAI

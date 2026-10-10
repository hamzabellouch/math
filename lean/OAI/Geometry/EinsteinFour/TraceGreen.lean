import OAI.Geometry.EinsteinFour.FlowGreen
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace OAI

/-! Integration of the full prescribed trace term, including its weight derivative. -/

namespace PositiveEinsteinFour.Averages

open MeasureTheory

noncomputable section

variable {Ω E : Type*} [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Integrate the trace block against the rough Laplacian. The gradient of
its coefficient is retained on the right-hand side. -/
theorem weighted_trace_green
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ i, Continuous (fun p : ℝ × Ω => φ i p.1 p.2))
    (hμ : ∀ i t, MeasurePreserving (φ i t) μ μ)
    (m : C(Ω, ℝ)) (dm : Fin 4 → C(Ω, ℝ))
    (B : C(Ω, E)) (dB Z dZ : Fin 4 → C(Ω, E))
    (hm : ∀ i t x, HasDerivAt (fun s => m (φ i s x)) (dm i (φ i t x)) t)
    (hB : ∀ i t x, HasDerivAt (fun s => B (φ i s x)) (dB i (φ i t x)) t)
    (hZ : ∀ i t x, HasDerivAt (fun s => Z i (φ i s x)) (dZ i (φ i t x)) t) :
    (∫ x, m x * inner ℝ (B x) (∑ i, dZ i x) +
      ∑ i, dm i x * inner ℝ (B x) (Z i x) ∂μ) =
      -(∫ x, m x * (∑ i, inner ℝ (dB i x) (Z i x)) ∂μ) := by
  have hL (i : Fin 4) : Integrable (fun x =>
      m x * inner ℝ (dB i x) (Z i x) + dm i x * inner ℝ (B x) (Z i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hR (i : Fin 4) : Integrable (fun x => m x * inner ℝ (B x) (dZ i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : (∫ x, ∑ i,
      (m x * inner ℝ (dB i x) (Z i x) + dm i x * inner ℝ (B x) (Z i x)) ∂μ) =
      -(∫ x, ∑ i, m x * inner ℝ (B x) (dZ i x) ∂μ) := by
    rw [integral_finsetSum _ (fun i _ => hL i),
      integral_finsetSum _ (fun i _ => hR i)]
    simp_rw [weighted_flow_green μ _ (hφ _) (hμ _) m (dm _) B (dB _) (Z _) (dZ _)
      (hm _) (hB _) (hZ _), Finset.sum_neg_distrib]
  have hJ : Integrable (fun x => m x * (∑ i, inner ℝ (dB i x) (Z i x))) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hK : Integrable (fun x => ∑ i, dm i x * inner ℝ (B x) (Z i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hQ : Integrable (fun x => m x * inner ℝ (B x) (∑ i, dZ i x)) μ :=
    (show Continuous _ by fun_prop).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← inner_sum] at hs
  rw [integral_add hJ hK] at hs
  rw [integral_add hQ hK]
  linarith

/-- Ordinary differentiation of the trace curvature coefficient. -/
theorem hasDerivAt_trace_block {v : ℝ → ℝ} {T N : ℝ → E}
    {dv : ℝ} {dT dN : E} {t : ℝ}
    (hv : HasDerivAt v dv t) (hT : HasDerivAt T dT t) (hN : HasDerivAt N dN t) :
    HasDerivAt (fun s => (4 + v s ^ 2) • T s - (5 : ℝ) • N s)
      ((4 + v t ^ 2) • dT + (2 * v t * dv) • T t - (5 : ℝ) • dN) t := by
  convert (((hasDerivAt_const t (4 : ℝ)).add (hv.pow 2)).smul hT).sub
    (hN.const_smul (5 : ℝ)) using 1
  simp only [Pi.add_apply, Pi.pow_apply, zero_add, Nat.cast_ofNat]
  module

/-- The derivative of `(4+v²)T-5N`, after `dN=2B_F(T)dT`, gives
exactly the normalized trace contribution used in equation (11). -/
theorem trace_derivative_pairing
    (T : E) (Z AZ : Fin 4 → E) (v e B : ℝ) (p : Fin 4 → ℝ)
    (he : (∑ i, ‖Z i‖ ^ 2) = 6 * e)
    (hB : (∑ i, inner ℝ (AZ i) (Z i)) = 6 * B)
    (hp : ∀ i, inner ℝ T (Z i) = 6 * v * p i) :
    (5 / 12 : ℝ) * (∑ i, inner ℝ
      ((4 + v ^ 2) • Z i + (2 * v * p i) • T - (10 : ℝ) • AZ i) (Z i)) =
        (10 + (5 / 2) * v ^ 2) * e - 25 * B + 5 * v ^ 2 * (∑ i, p i ^ 2) := by
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hp' : (∑ i, (2 * v * p i) * (6 * v * p i)) =
      12 * v ^ 2 * (∑ i, p i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← Finset.mul_sum, ← Finset.mul_sum, he, hB, hp']
  ring

/-- Both prescribed-trace subtractions integrate to the displayed
first-derivative contribution. All hypotheses are raw flow derivatives
and pointwise tensor contractions. -/
theorem weighted_trace_contribution
    (φ : Fin 4 → ℝ → Ω ≃ᵐ Ω)
    (hφ : ∀ i, Continuous (fun p : ℝ × Ω => φ i p.1 p.2))
    (hμ : ∀ i t, MeasurePreserving (φ i t) μ μ)
    (m : C(Ω, ℝ)) (dm : Fin 4 → C(Ω, ℝ))
    (B0 : C(Ω, E)) (dB0 Z dZ : Fin 4 → C(Ω, E))
    (T : Ω → E) (AZ : Fin 4 → Ω → E)
    (v e B : Ω → ℝ) (p : Fin 4 → Ω → ℝ)
    (hm : ∀ i t x, HasDerivAt (fun s => m (φ i s x)) (dm i (φ i t x)) t)
    (hB0 : ∀ i t x, HasDerivAt (fun s => B0 (φ i s x)) (dB0 i (φ i t x)) t)
    (hZ : ∀ i t x, HasDerivAt (fun s => Z i (φ i s x)) (dZ i (φ i t x)) t)
    (hdB0 : ∀ i x, dB0 i x = (4 + v x ^ 2) • Z i x +
      (2 * v x * p i x) • T x - (10 : ℝ) • AZ i x)
    (he : ∀ x, (∑ i, ‖Z i x‖ ^ 2) = 6 * e x)
    (hB : ∀ x, (∑ i, inner ℝ (AZ i x) (Z i x)) = 6 * B x)
    (hp : ∀ i x, inner ℝ (T x) (Z i x) = 6 * v x * p i x) :
    -(5 / 12 : ℝ) * (∫ x, m x * inner ℝ (B0 x) (∑ i, dZ i x) +
      ∑ i, dm i x * inner ℝ (B0 x) (Z i x) ∂μ) =
      ∫ x, m x * ((10 + (5 / 2) * v x ^ 2) * e x - 25 * B x +
        5 * v x ^ 2 * (∑ i, p i x ^ 2)) ∂μ := by
  rw [weighted_trace_green μ φ hφ hμ m dm B0 dB0 Z dZ hm hB0 hZ, neg_mul_neg,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have h := trace_derivative_pairing (T x) (fun i => Z i x) (fun i => AZ i x)
    (v x) (e x) (B x) (fun i => p i x) (he x) (hB x) (fun i => hp i x)
  simp only [← hdB0] at h
  calc
    _ = m x * ((5 / 12 : ℝ) * ∑ i, inner ℝ (dB0 i x) (Z i x)) := by ring
    _ = _ := by rw [h]

end

end PositiveEinsteinFour.Averages

end OAI

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # Moments from geometric level-set bounds -/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X]

/-- Geometrically decaying level measures yield a strong moment whenever
the decay exceeds the growth of the moment on successive levels. -/
theorem geometric_tail_moment (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {S B A q p : ℝ} (hS : 0 < S) (hB : 1 < B) (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hp : 0 < p) (hdecay : B^p*q < 1)
    (htail : ∀ k : ℕ, μ.real {x | S*B^k < f x} ≤ A*q^k) :
    Integrable (fun x => f x ^ p) μ ∧
      (∫ x, f x ^ p ∂μ) ≤ (S*B)^p * μ.real univ +
        A*(S*B^2)^p / (1-B^p*q) := by
  classical
  let E (k : ℕ) := {x | S*B^k < f x}
  let W (k : ℕ) := (S*B^(k+2))^p
  let G (k : ℕ) : X → ℝ≥0∞ := (E k).indicator (fun _ => ENNReal.ofReal (W k))
  let H := A*(S*B^2)^p
  let θ := B^p*q
  let M := (S*B)^p*μ.real univ + H/(1-θ)
  have hB0 : 0 < B := zero_lt_one.trans hB
  have hθ0 : 0 ≤ θ := mul_nonneg (Real.rpow_nonneg hB0.le _) hq
  have hθ1 : θ < 1 := hdecay
  have hH : 0 ≤ H := mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
  have hE (k : ℕ) : MeasurableSet (E k) := measurableSet_lt measurable_const hf
  have hG (k : ℕ) : Measurable (G k) := measurable_const.indicator (hE k)
  have hW (k : ℕ) : 0 ≤ W k := Real.rpow_nonneg (by positivity) _
  have hpoint (x : X) : ENNReal.ofReal (f x^p) ≤
      ENNReal.ofReal ((S*B)^p) + ∑' k, G k x := by
    by_cases hx : f x < S*B
    · apply le_trans _ le_self_add
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hf0 x) hx.le hp.le)
    · have hxSB : S*B ≤ f x := le_of_not_gt hx
      obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near
        ((le_div_iff₀ (mul_pos hS hB0)).mpr (by simpa using hxSB)) hB
      have hlow : S*B^k < f x := by
        have hh := (le_div_iff₀ (mul_pos hS hB0)).mp hk
        have hstrict : S*B^k < (S*B^k)*B := by
          nlinarith [mul_pos hS (pow_pos hB0 k)]
        nlinarith
      have hhigh : f x < S*B^(k+2) := by
        have hh := (div_lt_iff₀ (mul_pos hS hB0)).mp hk'
        rw [show k+2 = (k+1)+1 by omega, pow_succ]
        nlinarith
      calc
        _ ≤ ENNReal.ofReal (W k) :=
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hf0 x) hhigh.le hp.le)
        _ = G k x := by dsimp only [G]; rw [indicator_of_mem (show x ∈ E k from hlow)]
        _ ≤ ∑' j, G j x := ENNReal.le_tsum (f := fun j => G j x) k
        _ ≤ _ := le_add_self
  have hterm (k : ℕ) : (∫⁻ x, G k x ∂μ) ≤ ENNReal.ofReal (H*θ^k) := by
    rw [lintegral_indicator_const (hE k)]
    have hmeasure : μ (E k) ≤ ENNReal.ofReal (A*q^k) := by
      rw [← ofReal_measureReal (measure_ne_top μ (E k))]
      exact ENNReal.ofReal_le_ofReal (htail k)
    calc
      _ ≤ ENNReal.ofReal (W k)*ENNReal.ofReal (A*q^k) := mul_le_mul' le_rfl hmeasure
      _ = ENNReal.ofReal (W k*(A*q^k)) := (ENNReal.ofReal_mul (hW k)).symm
      _ = _ := by
        congr 1
        dsimp only [W, H, θ]
        rw [show k+2 = 2+k by omega, pow_add]
        rw [show S*(B^2*B^k) = (S*B^2)*B^k by ring,
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_pow_comm hB0.le p k, mul_pow]
        ring
  have hsum : Summable (fun k : ℕ => H*θ^k) :=
    (summable_geometric_of_lt_one hθ0 hθ1).mul_left H
  have htotal : (∫⁻ x, ENNReal.ofReal (f x^p) ∂μ) ≤ ENNReal.ofReal M := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal ((S*B)^p) + ∑' k, G k x ∂μ := lintegral_mono hpoint
      _ = ENNReal.ofReal ((S*B)^p)*μ univ + ∑' k, ∫⁻ x, G k x ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          lintegral_tsum (fun k => (hG k).aemeasurable)]
      _ ≤ ENNReal.ofReal ((S*B)^p)*μ univ + ∑' k, ENNReal.ofReal (H*θ^k) :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum hterm)
      _ = ENNReal.ofReal M := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hH (pow_nonneg hθ0 _)) hsum,
          tsum_mul_left, tsum_geometric_of_lt_one hθ0 hθ1,
          ← ofReal_measureReal (measure_ne_top μ univ),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        rfl
  have hfp : Measurable (fun x => f x^p) := hf.pow_const p
  have hfp0 : ∀ᵐ x ∂μ, 0 ≤ f x^p :=
    Eventually.of_forall fun x => Real.rpow_nonneg (hf0 x) p
  have hi : Integrable (fun x => f x^p) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hfp.aestronglyMeasurable hfp0).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top htotal)
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hfp0 hfp.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top htotal).trans_eq
    (ENNReal.toReal_ofReal (by dsimp only [M]; positivity))

end RegularPointCoordinates

end

end OAI

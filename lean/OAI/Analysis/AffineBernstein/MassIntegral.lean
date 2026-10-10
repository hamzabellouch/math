import Mathlib
import OAI.Analysis.AffineBernstein.ConvexGradientBound
import OAI.Analysis.AffineBernstein.MassInterpolation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/- The exact inverse-Hessian interpolation used in the source cell bound.
The two controlling integrals are the cap identity term and the true large
principal-minor term; no bound on the weighted integral is presumed. -/
lemma lintegral_weighted_tube_interpolation {n : ℕ} (hn : 1 ≤ n)
    {B Q t : X → ℝ} (hB : AEMeasurable B μ) (hQ : AEMeasurable Q μ)
    (ht : AEMeasurable t μ) (hBp : ∀ᵐ x ∂μ, 0 < B x)
    (hQp : ∀ᵐ x ∂μ, 0 < Q x) (htp : ∀ᵐ x ∂μ, 0 < t x) :
    (∫⁻ x, ENNReal.ofReal (Real.sqrt (B x*Q x)*t x) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (B x ^ (1/((n:ℝ)+2)) * Q x ^ (1-1/((n:ℝ)+2))*t x) ∂μ) ^
        (((n:ℝ)+2)/(2*((n:ℝ)+1))) *
      (∫⁻ x, ENNReal.ofReal (B x*t x) ∂μ) ^ (1-((n:ℝ)+2)/(2*((n:ℝ)+1))) := by
  have hp := weighted_tube_exponent hn
  have hf := ((hB.pow_const (1/((n:ℝ)+2))).mul (hQ.pow_const (1-1/((n:ℝ)+2)))).mul ht
  have hfp : ∀ᵐ x ∂μ, 0 ≤ B x ^ (1/((n:ℝ)+2))*Q x ^ (1-1/((n:ℝ)+2))*t x := by
    filter_upwards [hBp,hQp,htp] with x hx hy hz
    positivity
  have hgp : ∀ᵐ x ∂μ, 0 ≤ B x*t x := by
    filter_upwards [hBp,htp] with x hx hy
    positivity
  calc
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hBp,hQp,htp] with x hx hy hz
      rw [weighted_tube_interpolation (n := n) hx hy hz]
    _ ≤ _ := by
      simpa only [Pi.mul_apply] using
        lintegral_ofReal_geometric_mean_le μ hp.1 hp.2 hf (hB.mul ht) hfp hgp

/- Controlling the fiber area and the support height converts a positive
amount of affine area into a lower bound on the true invariant tube mass. -/
lemma lintegral_tube_area_le_mass {n : ℕ} (hn : 1 ≤ n)
    {h B Q : X → ℝ} (hh : AEMeasurable h μ) (hB : AEMeasurable B μ)
    (hQ : AEMeasurable Q μ) (hhp : ∀ᵐ x ∂μ, 0 < h x)
    (hBp : ∀ᵐ x ∂μ, 0 < B x) (hQp : ∀ᵐ x ∂μ, 0 < Q x)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂μ, h x ≤ M) :
    (∫⁻ x, ENNReal.ofReal (B x ^ (1/((n:ℝ)+2)) * Q x ^ (1-1/((n:ℝ)+2))) ∂μ) ≤
      ENNReal.ofReal (M ^ ((n:ℝ)/((n:ℝ)+2))) *
      (∫⁻ x, ENNReal.ofReal (tubeMeasureCoefficient n (h x) (B x) (Q x)) ∂μ)^(2/((n:ℝ)+2)) *
      (∫⁻ x, ENNReal.ofReal (Q x) ∂μ)^(1-2/((n:ℝ)+2)) := by
  let p : ℝ := 2/((n:ℝ)+2)
  let W := fun x => tubeMeasureCoefficient n (h x) (B x) (Q x)
  have hp : 0 < p := by dsimp [p]; positivity
  have hp1 : p < 1 := by
    dsimp [p]
    apply (div_lt_one (by positivity)).2
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hW : AEMeasurable W μ :=
    (hh.pow_const (-(n:ℝ)/2)).mul ((hB.mul hQ).sqrt)
  have hWp : ∀ᵐ x ∂μ, 0 ≤ W x := by
    filter_upwards [hhp,hBp,hQp] with x hx hy hz
    exact (tubeMeasureCoefficient_pos hx hy hz).le
  have hQn := hQp.mono fun _ hx => hx.le
  have hholder := lintegral_ofReal_geometric_mean_le μ hp hp1 hW hQ hWp hQn
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (M ^ ((n:ℝ)/((n:ℝ)+2))) *
        ENNReal.ofReal ((W x)^p*(Q x)^(1-p)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hhp,hBp,hQp,hbound] with x hx hy hz hb
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]
      apply ENNReal.ofReal_le_ofReal
      rw [tube_area_factorization hx hy hz]
      have hm : (h x)^((n:ℝ)/((n:ℝ)+2)) ≤ M^((n:ℝ)/((n:ℝ)+2)) :=
        Real.rpow_le_rpow hx.le hb (by positivity)
      change (W x)^p * (h x)^((n:ℝ)/((n:ℝ)+2)) * (Q x)^(1-p) ≤ _
      calc
        _ ≤ (W x)^p * M^((n:ℝ)/((n:ℝ)+2)) * (Q x)^(1-p) := by
          have hw : 0 ≤ W x := (tubeMeasureCoefficient_pos hx hy hz).le
          gcongr
        _ = _ := by ring
    _ = ENNReal.ofReal (M ^ ((n:ℝ)/((n:ℝ)+2))) *
        ∫⁻ x, ENNReal.ofReal ((W x)^p*(Q x)^(1-p)) ∂μ := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_right hholder
        (ENNReal.ofReal (M ^ ((n:ℝ)/((n:ℝ)+2))))

end AffineBernstein
end

end OAI

import OAI.Analysis.LipschitzHilbert.Fourier.LatticeCoefficientConvolution
import OAI.Analysis.LipschitzHilbert.Estimates.MultiplierError

namespace OAI

/-! The fixed-scale convolution majorant for coefficients of the actual
angular multiplier error, including its two-coordinate direction profile. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

def angularErrorWave {ι κ : Type*} (b : ι → κ → ℝ → ℂ)
    (ψ : ι → κ → ℝ × ℝ → ℂ) (u : ℝ × ℝ → ℝ) (t d : ℝ)
    (i : ι) (k : κ) (z : ℝ × ℝ) : ℂ :=
  multiplierError (b i k) t d (u z) * ψ i k z

theorem angularErrorWave_measurable {ι κ : Type*}
    (b : ι → κ → ℝ → ℂ) (ψ : ι → κ → ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → ℝ) (t d : ℝ)
    (hb : ∀ i k, Measurable (b i k)) (hψ : ∀ i k, Measurable (ψ i k))
    (hu : Measurable u) (i : ι) (k : κ) :
    Measurable (angularErrorWave b ψ u t d i k) := by
  have huabs : Measurable (fun z => |u z-t|) := by
    simpa only [Real.norm_eq_abs] using (hu.sub_const t).norm
  have hsel : MeasurableSet {z | |u z-t| ≤ d} :=
    measurableSet_le huabs measurable_const
  exact ((hb i k |>.comp hu).sub
    (Measurable.ite hsel measurable_const measurable_const)).mul (hψ i k)

theorem angular_error_coefficient_convolution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site) (a z0 l W : ℝ)
    (hl : 0 < l) (hW : 0 < W)
    (b : ι → κ → ℝ → ℂ) (ψ : ι → κ → ℝ × ℝ → ℂ)
    (u : ℝ × ℝ → ℝ) (hu : Measurable u) (t d c R C M L : ℝ)
    (hd : 0 < d) (hc : 0 < c) (hc1 : c ≤ 1) (hR : 1 ≤ R)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hb : ∀ i k, Measurable (b i k)) (hψ : ∀ i k, Measurable (ψ i k))
    (hbM : ∀ i k s, ‖b i k s‖ ≤ M)
    (hnear : ∀ i k s, |s-t| ≤ c*d → ‖b i k s-b i k t‖ ≤ L*(|s-t|/d))
    (hfar : ∀ i k s, R*d < |s-t| → b i k s = 0)
    (hψC : ∀ i k z, ‖ψ i k z‖ ≤ C *
      tileEnvelope (a+l*(site i).1) (z0+W*(site i).2) l W 6 z)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ × ℝ) :
    (∑ i, ‖analyzingCoefficient volume (fun _ : ι => l*W)
      (angularErrorWave b ψ u t d) g i‖ *
      tileEnvelope (a+l*(site i).1) (z0+W*(site i).2) l W 6 z) ≤
      (64*(4*Real.pi)^2) * planarPositiveConvolution l W
        (fun p => (C*(2*M+L))*errorSourceProfile c R d |u p-t|) z.1 z.2 := by
  let f := fun p : ℝ × ℝ => (C*(2*M+L))*errorSourceProfile c R d |u p-t|
  have hA : 0 ≤ C*(2*M+L) := by positivity
  have huabs : Measurable (fun p => |u p-t|) := by
    simpa only [Real.norm_eq_abs] using (hu.sub_const t).norm
  have hf : Measurable f :=
    (errorSourceProfile_measurable huabs c R d).const_mul _
  have hf0 (p : ℝ × ℝ) : 0 ≤ f p :=
    mul_nonneg hA (errorSourceProfile_nonneg c R d _ hd (abs_nonneg _))
  have hfb (p : ℝ × ℝ) : ‖f p‖ ≤ (C*(2*M+L))*(1+c) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 p)]
    exact mul_le_mul_of_nonneg_left (errorSourceProfile_bound c R d _ hc hd (abs_nonneg _)) hA
  have hbound (i : ι) (k : κ) (p : ℝ × ℝ) : ‖angularErrorWave b ψ u t d i k p‖ ≤
      tileEnvelope (a+l*(site i).1) (z0+W*(site i).2) l W 6 p * f p := by
    have he := multiplierError_bound (b i k) t d c R M L (u p)
      hd hc hc1 hR hM hL (hbM i k) (hnear i k (u p)) (hfar i k (u p))
    rw [angularErrorWave, norm_mul]
    have hm := mul_le_mul he (hψC i k p) (norm_nonneg _)
      (mul_nonneg (by positivity) (errorSourceProfile_nonneg c R d _ hd (abs_nonneg _)))
    convert hm using 1
    dsimp [f]
    ring
  exact lattice_coefficient_convolution site hinj a z0 l W hl hW f hf hf0 hfb
    (angularErrorWave b ψ u t d) (angularErrorWave_measurable b ψ u t d hb hψ hu)
    hbound g hg hg1 z

end LipschitzHilbert

end

end OAI

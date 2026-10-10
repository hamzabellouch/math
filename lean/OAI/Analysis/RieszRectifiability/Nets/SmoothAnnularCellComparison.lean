import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.SmoothAnnularWeights
import OAI.Analysis.RieszRectifiability.Foundations.AnnularAverageComparison

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def smoothAnnularTransform {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (a : Ambient d)
    (r R : ℝ) (hr : 0 < r) (hR : 0 < R) : Ambient d :=
  ∫ y, smoothAnnularWeight a r R hr hR y • kernel n a y ∂μ

theorem truncated_smoothAnnular_at_center {d : ℕ} (n : ℕ) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r R ε : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hε : ε < r) :
    truncated n μ ε (smoothAnnularWeight a r R hr (hr.trans_le hrR)) a =
      smoothAnnularTransform n μ a r R hr (hr.trans_le hrR) := by
  have hs := (smoothAnnularWeight_properties n G μ hg a r R hr hrR).2.2.1
  unfold truncated smoothAnnularTransform
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hzero : smoothAnnularWeight a r R hr (hr.trans_le hrR) y = 0 := by
    by_contra hne
    have hd := hs y hne
    exact hy (hε.trans_le hd)
  rw [hzero, zero_smul]

theorem smooth_annular_indicator_cell_comparison {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G L : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a e : Ambient d) (he : ‖e‖ ≤ 1)
    (r R ε : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hε : 0 < ε) (hεr : ε < r / 2)
    (S : Set (Ambient d)) (hS : MeasurableSet S) (hSfin : μ S < ∞)
    (hcontains : ball a (2 * R) ⊆ S)
    (A Q : Set (Ambient d)) (hA : MeasurableSet A) (hQ : MeasurableSet Q)
    (hAfin : μ A < ∞) (hQfin : μ Q < ∞) (hApos : 0 < μ.real A) (hQpos : 0 < μ.real Q)
    (hAnear : ∀ x ∈ A, 2 * dist x a ≤ r) (hQnear : ∀ x ∈ Q, 2 * dist x a ≤ R)
    (hAmass : r ^ n ≤ L * μ.real A) (hQmass : R ^ n ≤ L * μ.real Q)
    (D : ℝ≥0)
    (hRiesz : ∀ u : Ambient d → ℝ, MemLp u 2 μ →
      MemLp (truncated n μ ε u) 2 μ ∧
        eLpNorm (truncated n μ ε u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) :
    |inner ℝ e (smoothAnnularTransform n μ a r R hr (hr.trans_le hrR))| ≤
      |cellMean (μ.restrict A) (fun x => inner ℝ e
          (truncated n μ ε (S.indicator (fun _ => 1)) x)) -
        cellMean (μ.restrict Q) (fun x => inner ℝ e
          (truncated n μ ε (S.indicator (fun _ => 1)) x))| +
      3 * ((D : ℝ) ^ 2 * (G * 2 ^ n * L) + 1) + 3 * exteriorCellMeanConstant n G 1 := by
  let f : Ambient d → ℝ := annularSmoothBallCutoff a r hr
  let g := smoothAnnularWeight a r R hr (hr.trans_le hrR)
  let h := smoothExteriorWeight a R (hr.trans_le hrR) S
  have hf := annularSmoothBallCutoff_energy n G μ hg a r hr
  have hg' := smoothAnnularWeight_properties n G μ hg a r R hr hrR
  have hh := smoothExteriorWeight_properties n G μ hg a R (hr.trans_le hrR) S hS hSfin hcontains
  have hGN : 0 ≤ G * (2 : ℝ) ^ n := mul_nonneg hg.1 (by positivity)
  have hlocal (t : ℝ) (B : Set (Ambient d)) (ht : t ^ n ≤ L * μ.real B) :
      G * (2 * t) ^ n ≤ (G * 2 ^ n * L) * μ.real B := by
    calc
      _ = (G * 2 ^ n) * t ^ n := by rw [mul_pow]; ring
      _ ≤ (G * 2 ^ n) * (L * μ.real B) := mul_le_mul_of_nonneg_left ht hGN
      _ = _ := by ring
  have hfA : (∫ y, f y ^ 2 ∂μ) ≤ (G * 2 ^ n * L) * μ.real A :=
    hf.2.trans (hlocal r A hAmass)
  have hfQ : (∫ y, f y ^ 2 ∂μ) ≤ (G * 2 ^ n * L) * μ.real Q :=
    hf.2.trans (hlocal r Q ((pow_le_pow_left₀ hr.le hrR n).trans hQmass))
  have hgQ : (∫ y, g y ^ 2 ∂μ) ≤ (G * 2 ^ n * L) * μ.real Q :=
    hg'.2.2.2.trans (hlocal R Q hQmass)
  have hb := annular_cell_average_comparison n hn G 1 (G * 2 ^ n * L) μ hg ε r R
    hε hr hrR hεr f g h hf.1 hg'.1 hh.1 (by norm_num) hg'.2.1 hh.2.1
    a e he hg'.2.2.1 hh.2.2 A Q hA hQ hAfin hQfin hApos hQpos hAnear hQnear
    hfA hfQ hgQ D hRiesz
  have heq : (fun y => f y + g y + h y) = S.indicator (fun _ => 1) :=
    funext (smoothAnnularWeights_sum a r R hr (hr.trans_le hrR) S)
  rw [heq] at hb
  change |inner ℝ e (truncated n μ ε (smoothAnnularWeight a r R hr (hr.trans_le hrR)) a)| ≤ _ at hb
  rwa [truncated_smoothAnnular_at_center n G μ hg a r R ε hr hrR (by linarith)] at hb

end

end RieszRectifiability

end OAI

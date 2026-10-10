import OAI.Analysis.LipschitzHilbert.Fourier.TileEnvelopeKernel
import OAI.Analysis.LipschitzHilbert.Packets.AnalyzingCoefficientNorm

namespace OAI

/-! Actual analyzing coefficients controlled by a common scalar source
satisfy the fixed-scale positive convolution estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace LipschitzHilbert

theorem lattice_coefficient_convolution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (site : ι → ℤ × ℤ) (hinj : Function.Injective site) (a b l W : ℝ)
    (hl : 0 < l) (hW : 0 < W) (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ z, 0 ≤ f z) {M : ℝ} (hfb : ∀ z, ‖f z‖ ≤ M)
    (wave : ι → κ → ℝ × ℝ → ℂ) (hw : ∀ i k, Measurable (wave i k))
    (hwf : ∀ i k z, ‖wave i k z‖ ≤
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z * f z)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (z : ℝ × ℝ) :
    (∑ i, ‖analyzingCoefficient volume (fun _ : ι => l*W) wave g i‖ *
      tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6 z) ≤
      (64 * (4*Real.pi)^2) * planarPositiveConvolution l W f z.1 z.2 := by
  let E := fun i => tileEnvelope (a+l*(site i).1) (b+W*(site i).2) l W 6
  have hEi (i : ι) : Integrable (fun p => E i p * f p) :=
    (tileEnvelope_integrable _ _ _ _ (by decide : 1 ≤ 6) hl hW).mul_bdd
      hf.aestronglyMeasurable (Filter.Eventually.of_forall hfb)
  have hEn (i : ι) (p : ℝ × ℝ) : 0 ≤ E i p := tileEnvelope_nonneg _ _ _ _ _ _
  have hint (i : ι) (k : κ) : Integrable (fun p => g p k * conj (wave i k p)) := by
    have hgm : Measurable (fun p => g p k) :=
      (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
    apply (hEi i).mono' (hgm.mul (continuous_star.measurable.comp (hw i k))).aestronglyMeasurable
    filter_upwards [] with p
    dsimp only [Pi.mul_apply, Function.comp_apply]
    rw [norm_mul, norm_star]
    have hgk := (PiLp.norm_apply_le (g p) k).trans (hg1 p)
    exact (mul_le_mul_of_nonneg_right hgk (norm_nonneg _)).trans
      (by simpa only [one_mul] using hwf i k p)
  have ha (i : ι) : ‖analyzingCoefficient volume (fun _ : ι => l*W) wave g i‖ ≤
      (l*W)⁻¹ * ∫ p, E i p * f p :=
    analyzingCoefficient_norm_le volume (fun _ : ι => l*W) wave g i (fun p => E i p * f p)
      (mul_pos hl hW) (hEi i) (fun p => mul_nonneg (hEn i p) (hf0 p))
      (hint i) hg1 (hwf i)
  have hsumI : Integrable (fun p => ∑ i, (E i z * E i p / (l*W)) * f p) := by
    apply integrable_finsetSum
    intro i _
    convert (hEi i).const_mul (E i z / (l*W)) using 1
    funext p
    ring
  have hkerI := planarPositiveConvolution_integrable l W f hf hl hW hfb z.1 z.2
  calc
    _ ≤ ∑ i, ((l*W)⁻¹ * ∫ p, E i p * f p) * E i z :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (ha i) (hEn i z))
    _ = ∫ p, ∑ i, (E i z * E i p / (l*W)) * f p := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i _
        have heq : (fun p => (E i z * E i p / (l*W)) * f p) =
            (fun p => (E i z / (l*W)) * (E i p * f p)) := by funext p; ring
        rw [heq, integral_const_mul]
        ring
      · intro i _
        convert (hEi i).const_mul (E i z / (l*W)) using 1
        funext p
        ring
    _ ≤ ∫ p, (64*(4*Real.pi)^2) *
        ((lineKernel l (z.1-p.1) * lineKernel W (z.2-p.2)) * f p) := by
      apply integral_mono hsumI (hkerI.const_mul _)
      intro p
      have h := mul_le_mul_of_nonneg_right
        (two_point_tile_kernel site hinj a b l W hl hW z p) (hf0 p)
      convert h using 1
      · simp only [Finset.sum_mul, Finset.sum_div]
        rfl
      · ring
    _ = _ := integral_const_mul _ _

end LipschitzHilbert

end

end OAI

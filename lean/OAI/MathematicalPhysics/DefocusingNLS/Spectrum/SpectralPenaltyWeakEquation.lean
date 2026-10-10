import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCoreTestExtension
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicFormLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPressureAway

namespace OAI

/-! A weak limit of the penalized equations satisfies the limiting constrained equation. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralHarmonicPenalty_weak_equation (ell : ℕ) (R l : ℝ)
    (hl : 0 < l) (hlR : l < R) (w : ℕ → SpectralHarmonicWeight R)
    (w₀ : SpectralHarmonicWeight R) (δ : ℕ → ℝ) (hδ : ∀ n, 0 ≤ δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hwr : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, ‖(w n).density r-w₀.density r‖ ≤ δ n)
    (hwa : ∀ n, ∀ᵐ r ∂spectralAngularMeasure R, ‖(w n).density r-w₀.density r‖ ≤ δ n)
    (p : ℕ → ℝ → ℝ) (hpm : ∀ n, AEStronglyMeasurable (p n) (radialPressureMeasure R))
    (hpb : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, ‖p n r‖ ≤ 1) (a : ℕ → ℝ)
    (haway : ∀ d : ℝ, 0 < d → ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧
      Tendsto η atTop (𝓝 0) ∧ ∀ n, ∀ᵐ r ∂radialPressureMeasure R,
        l+d < r → ‖(a n)⁻¹*((w n).density r*p n r)‖ ≤ η n)
    (F : ℕ → StrongDual ℝ (SpectralHarmonicPair ell R))
    (F₀ : StrongDual ℝ (SpectralHarmonicPair ell R))
    (hF : ∀ v, Tendsto (fun n => F n v) atTop (𝓝 (F₀ v)))
    (u : ℕ → SpectralHarmonicPair ell R) (u₀ : SpectralHarmonicPair ell R)
    (M : ℝ) (hM : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ L : SpectralHarmonicPair ell R →L[ℝ] ℝ,
      Tendsto (fun n => L (u n)) atTop (𝓝 (L u₀)))
    (he : ∀ n v, spectralHarmonicPairForm ell R (w n) (u n) v+
      (a n)⁻¹*inner ℝ (spectralWeightedPressure R (w n) (p n) (hpm n) (hpb n)
        (spectralHarmonicFirstValue ell R (u n))) (spectralHarmonicFirstValue ell R v)=F n v) :
    ∀ v ∈ spectralHarmonicCoreSubspace ell R l, spectralHarmonicPairForm ell R w₀ u₀ v=F₀ v := by
  apply spectralHarmonicCore_equation_of_separated ell R l hl hlR w₀ u₀ F₀
  intro d hd v hv
  obtain ⟨η,hη,hη0,hηb⟩ := haway d hd
  have hv0 := (spectralHarmonicCore_mem ell R (l+d) v).mp hv
  have hV (n : ℕ) : ‖spectralHarmonicFirstValue ell R (u n)‖ ≤ M := by
    exact ((spectralHarmonicCoordinate_norms ell R (u n).fst).1.trans
      (WithLp.norm_fst_le _ (u n))).trans (hM n)
  have hP : Tendsto (fun n => (a n)⁻¹*inner ℝ
      (spectralWeightedPressure R (w n) (p n) (hpm n) (hpb n) (spectralHarmonicFirstValue ell R (u n)))
      (spectralHarmonicFirstValue ell R v)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (show Tendsto (fun n => M*(η n*‖spectralHarmonicFirstValue ell R v‖)) atTop (𝓝 0) from by
        simpa only [zero_mul,mul_zero] using tendsto_const_nhds.mul
          (hη0.mul_const ‖spectralHarmonicFirstValue ell R v‖))
    exact (spectralWeightedPressure_offCore_inner R (l+d) (a n) (η n) (w n)
      (p n) (hpm n) (hpb n) (hηb n) _ _ hv0).trans
      (mul_le_mul_of_nonneg_right (hV n) (mul_nonneg (hη n) (norm_nonneg _)))
  have hB := spectralHarmonicPairForm_tendsto ell R w w₀ δ hδ hδ0 hwr hwa u u₀ M hM hweak v
  have hsum := hB.add hP
  simp only [add_zero,he] at hsum
  exact tendsto_nhds_unique hsum (hF v)

end DefocusingNLS

end OAI

import OAI.Analysis.LipschitzHilbert.Estimates.ShearedLatticePeriodization

namespace OAI

/-! Averaging actual packet sums over one sheared lattice cell.
The probability normalization leaves precisely one inverse area per packet. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate Topology BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem averaged_packet_identity (KA KB f b g : ℝ × ℝ → ℂ)
    (hA : Integrable KA planeMeasure) (hB : Integrable KB planeMeasure)
    (hf : Integrable f planeMeasure) (hb : Measurable b) (hg : Measurable g)
    (Mb Mg : ℝ) (hbb : ∀ x, ‖b x‖≤Mb) (hgb : ∀ x, ‖g x‖≤Mg)
    (l W theta : ℝ) (hl : 0<l) (hW : 0<W) :
    (∫ x, b x*kernelConvolution KA (kernelConvolution KB f) x*conj (g x) ∂planeMeasure) =
      ∫ z, ∑' n : ℤ×ℤ, ((l*W:ℝ):ℂ)⁻¹ *
        packetProduct KA KB f b g (l*W) (latticeHom l W theta n+z)
        ∂latticeAverage l W theta := by
  let F := packetProduct KA KB f b g (l*W)
  have hF : Integrable F planeMeasure := packetProduct_integrable KA KB f b g
    hA hB hf hb hg Mb Mg hbb hgb (l*W)
  have hp := continuous_packet_identity KA KB f b g hA hB hf hb hg Mb Mg hbb hgb
    (l*W) (mul_pos hl hW).ne'
  have ht := sheared_lattice_periodization (theta := theta) hl hW F hF
  have hnorm : (∫ z, ∑' n : ℤ×ℤ, ((l*W:ℝ):ℂ)⁻¹ * F (latticeHom l W theta n+z)
      ∂latticeAverage l W theta) =
      (((l*W:ℝ):ℂ)^2)⁻¹ * ∫ z, F z ∂planeMeasure := by
    rw [integral_latticeAverage hl hW]
    simp_rw [tsum_mul_left]
    rw [integral_const_mul, ← ht]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, pow_two, mul_inv_rev]
    ring
  exact hp.trans hnorm.symm

/-- Uniform bounds for the finite packet forms pass to the actual averaged
convolution form. Absolute convergence, rather than a cardinality bound,
justifies the passage through the infinite spatial lattice. -/
theorem averaged_packet_bound (KA KB f b g : ℝ × ℝ → ℂ)
    (hA : Integrable KA planeMeasure) (hB : Integrable KB planeMeasure)
    (hf : Integrable f planeMeasure) (hb : Measurable b) (hg : Measurable g)
    (Mb Mg : ℝ) (hbb : ∀ x, ‖b x‖≤Mb) (hgb : ∀ x, ‖g x‖≤Mg)
    (l W theta C : ℝ) (hl : 0<l) (hW : 0<W)
    (hfinite : ∀ z (I : Finset (ℤ×ℤ)),
      ‖∑ n∈I, ((l*W:ℝ):ℂ)⁻¹ *
        packetProduct KA KB f b g (l*W) (latticeHom l W theta n+z)‖≤C) :
    ‖∫ x, b x*kernelConvolution KA (kernelConvolution KB f) x*conj (g x) ∂planeMeasure‖≤C := by
  let F := packetProduct KA KB f b g (l*W)
  have hF := packetProduct_integrable KA KB f b g hA hB hf hb hg Mb Mg hbb hgb (l*W)
  have hs := sheared_lattice_summable (theta := theta) hl hW F hF
  have hn : ∀ᵐ z ∂latticeAverage l W theta,
      ‖∑' n : ℤ×ℤ, ((l*W:ℝ):ℂ)⁻¹ * F (latticeHom l W theta n+z)‖≤C := by
    filter_upwards [hs] with z hz
    have ht := (hz.of_norm.mul_left (((l*W:ℝ):ℂ)⁻¹)).hasSum
    exact le_of_tendsto ht.norm (Filter.Eventually.of_forall (hfinite z))
  let := latticeAverage_probability (theta := theta) hl hW
  rw [averaged_packet_identity KA KB f b g hA hB hf hb hg Mb Mg hbb hgb l W theta hl hW]
  simpa using norm_integral_le_of_norm_le_const hn

end LipschitzHilbert.PacketRepresentation

end

end OAI

import OAI.Analysis.LipschitzHilbert.Estimates.JointLatticeAverage

namespace OAI

/-! All carrier components share the same site at each scale and direction.
Averaging preserves the vector packet estimate without a dimension factor. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

theorem joint_vector_convolution_packet_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (KA KB f b g : ι → κ → (ℝ×ℝ) → ℂ)
    (hA : ∀ i k, Integrable (KA i k) planeMeasure)
    (hB : ∀ i k, Integrable (KB i k) planeMeasure)
    (hf : ∀ i k, Integrable (f i k) planeMeasure)
    (hb : ∀ i k, Measurable (b i k)) (hg : ∀ i k, Measurable (g i k))
    (Mb Mg : ι → κ → ℝ)
    (hbb : ∀ i k x, ‖b i k x‖≤Mb i k) (hgb : ∀ i k x, ‖g i k x‖≤Mg i k)
    (l W theta : ι → ℝ) (hl : ∀ i, 0<l i) (hW : ∀ i, 0<W i)
    (C : ℝ)
    (hfinite : ∀ z : ι → (ℝ×ℝ), ∀ S : Finset (ι×(ℤ×ℤ)),
      ‖∑ p ∈ S, ∑ k, ((l p.1*W p.1:ℝ):ℂ)⁻¹*
        packetProduct (KA p.1 k) (KB p.1 k) (f p.1 k) (b p.1 k) (g p.1 k)
          (l p.1*W p.1) (latticeHom (l p.1) (W p.1) (theta p.1) p.2+z p.1)‖≤C) :
    ‖∑ i, ∑ k, ∫ x, b i k x*
      kernelConvolution (KA i k) (kernelConvolution (KB i k) (f i k)) x*
      conj (g i k x) ∂planeMeasure‖≤C := by
  let F := fun i z => ∑ k, packetProduct (KA i k) (KB i k) (f i k) (b i k) (g i k)
    (l i*W i) z
  have hprod (i : ι) (k : κ) :
      Integrable (packetProduct (KA i k) (KB i k) (f i k) (b i k) (g i k) (l i*W i))
        planeMeasure :=
    packetProduct_integrable (KA i k) (KB i k) (f i k) (b i k) (g i k)
      (hA i k) (hB i k) (hf i k) (hb i k) (hg i k)
      (Mb i k) (Mg i k) (hbb i k) (hgb i k) (l i*W i)
  have hF (i : ι) : Integrable (F i) planeMeasure :=
    integrable_finsetSum _ (fun k _ => hprod i k)
  have h := joint_lattice_average_bound l W theta hl hW F hF C (by
    intro z S
    simpa only [F,Finset.mul_sum] using hfinite z S)
  have heq (i : ι) : (∑ k, ∫ x, b i k x*
      kernelConvolution (KA i k) (kernelConvolution (KB i k) (f i k)) x*
      conj (g i k x) ∂planeMeasure) =
      (((l i*W i:ℝ):ℂ)^2)⁻¹*∫ z, F i z ∂planeMeasure := by
    simp only [F]
    rw [integral_finsetSum _ (fun k _ => hprod i k),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact continuous_packet_identity (KA i k) (KB i k) (f i k) (b i k) (g i k)
      (hA i k) (hB i k) (hf i k) (hb i k) (hg i k)
      (Mb i k) (Mg i k) (hbb i k) (hgb i k) (l i*W i) (mul_pos (hl i) (hW i)).ne'
  simpa only [heq] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI

import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinLpEnergy

namespace OAI

/-! Actual finite vectors of vertical projections, including their energy,
L1, uniform, and horizontal support bounds. -/
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform
namespace LipschitzHilbert.PacketRepresentation

def verticalBinKernelCost : ℝ := ∫ t : ℝ, ‖(𝓕⁻ verticalBinProfile : SchwartzMap ℝ ℂ) t‖

def verticalBinVector (I : Finset ℕ) (K : ℕ) (W : ℝ) (f : ℝ×ℝ → ℂ)
    (z : ℝ×ℝ) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun n : I => verticalConvolution
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z)

theorem euclidean_norm_le_sum {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) :
    ‖v‖≤∑ i, ‖v i‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

theorem verticalBinVector_norm_le_sum (I : Finset ℕ) (K : ℕ) (W : ℝ) (f : ℝ×ℝ → ℂ)
    (z : ℝ×ℝ) :
    ‖verticalBinVector I K W f z‖≤∑ n∈I, ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖ := by
  have h := euclidean_norm_le_sum (verticalBinVector I K W f z)
  change ‖verticalBinVector I K W f z‖≤∑ n : I, ‖verticalConvolution
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖ at h
  rw [Finset.sum_coe_sort I (fun n : ℕ => ‖verticalConvolution
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖)] at h
  exact h

theorem verticalBinVector_measurable (I : Finset ℕ) (K : ℕ) (W : ℝ)
    (f : ℝ×ℝ → ℂ) (hf : Measurable f) : Measurable (verticalBinVector I K W f) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro n
  exact verticalConvolution_measurable _ (verticalProfileKernel_continuous _ _ _).measurable f hf

theorem verticalBinVector_energy (I : Finset ℕ) (K : ℕ) (W : ℝ) (hW : 0<W)
    (hI : I⊆Finset.range (2*K+1)) (f : ℝ×ℝ → ℂ) (hfm : Measurable f)
    (hf : MemLp f 2 planeMeasure) :
    MemLp (verticalBinVector I K W f) 2 planeMeasure ∧
      (∫ z, ‖verticalBinVector I K W f z‖^2 ∂planeMeasure)≤∫ z, ‖f z‖^2 ∂planeMeasure := by
  have hi (n : ℕ) : Integrable (fun z => ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖^2) planeMeasure :=
    (verticalConvolution_energy_bound _ (verticalProfileKernel_integrable _ _ _ hW)
      (verticalProfileKernel_continuous _ _ _).measurable f hfm hf).1.integrable_norm_pow (by decide : 2≠0)
  have heq (z : ℝ×ℝ) : ‖verticalBinVector I K W f z‖^2=∑ n∈I, ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ n : I, ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖^2)=_
    exact Finset.sum_coe_sort I (fun n : ℕ => ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖^2)
  have hint : Integrable (fun z => ‖verticalBinVector I K W f z‖^2) planeMeasure := by
    simp_rw [heq]
    exact integrable_finsetSum I (fun n _ => hi n)
  refine ⟨(memLp_two_iff_integrable_sq_norm (verticalBinVector_measurable I K W f hfm).aestronglyMeasurable).2 hint,?_⟩
  simp_rw [heq]
  rw [integral_finsetSum I (fun n _ => hi n)]
  exact verticalBin_measurable_energy f hfm hf K W hW I hI

theorem verticalBinVector_l1 (I : Finset ℕ) (K : ℕ) (W : ℝ) (hW : 0<W)
    (f : ℝ×ℝ → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (verticalBinVector I K W f) planeMeasure ∧
      (∫ z, ‖verticalBinVector I K W f z‖ ∂planeMeasure)≤
        I.card*verticalBinKernelCost*(∫ z, ‖f z‖ ∂planeMeasure) := by
  have hi (n : ℕ) := verticalConvolution_integrable
    (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n))
    (verticalProfileKernel_integrable _ _ _ hW)
    (verticalProfileKernel_continuous _ _ _).measurable f hfm hf
  have hs : Integrable (fun z => ∑ n∈I, ‖verticalConvolution
      (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖) planeMeasure :=
    integrable_finsetSum I (fun n _ => (hi n).norm)
  have hv : Integrable (verticalBinVector I K W f) planeMeasure :=
    hs.mono' (verticalBinVector_measurable I K W f hfm).aestronglyMeasurable
      (Filter.Eventually.of_forall (verticalBinVector_norm_le_sum I K W f))
  refine ⟨hv,?_⟩
  calc
    _ ≤ ∫ z, ∑ n∈I, ‖verticalConvolution
        (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖ ∂planeMeasure :=
      integral_mono hv.norm hs (verticalBinVector_norm_le_sum I K W f)
    _ = ∑ n∈I, ∫ z, ‖verticalConvolution
        (verticalProfileKernel verticalBinProfile W (verticalBinCenter K W n)) f z‖ ∂planeMeasure :=
      integral_finsetSum I (fun n _ => (hi n).norm)
    _ ≤ ∑ _n∈I, verticalBinKernelCost*(∫ z, ‖f z‖ ∂planeMeasure) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [verticalBinKernelCost,verticalProfileKernel,
        modulatedTimeKernel_l1 _ W _ hW] using
        verticalConvolution_l1_bound _ (verticalProfileKernel_integrable _ _ _ hW)
          (verticalProfileKernel_continuous _ _ _).measurable f hfm hf
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem verticalBinVector_uniform (I : Finset ℕ) (K : ℕ) (W : ℝ) (hW : 0<W)
    (f : ℝ×ℝ → ℂ) (M : ℝ) (hf : ∀ z, ‖f z‖≤M) (z : ℝ×ℝ) :
    ‖verticalBinVector I K W f z‖≤I.card*verticalBinKernelCost*M := by
  apply (verticalBinVector_norm_le_sum I K W f z).trans
  calc
    _ ≤ ∑ _n∈I, M*verticalBinKernelCost := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [verticalBinKernelCost,verticalProfileKernel,
        modulatedTimeKernel_l1 _ W _ hW] using
        verticalConvolution_uniform_bound _ (verticalProfileKernel_integrable _ _ _ hW) f M hf z
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

theorem verticalBinVector_horizontal_support (I : Finset ℕ) (K : ℕ) (W : ℝ)
    (f : ℝ×ℝ → ℂ) (S : Set ℝ) (hf : ∀ z, z.1∉S → f z=0) :
    ∀ z, z.1∉S → verticalBinVector I K W f z=0 := by
  intro z hz
  apply (WithLp.ext_iff 2).mpr
  funext n
  exact verticalConvolution_horizontal_support _ f S hf z hz

end LipschitzHilbert.PacketRepresentation

end

end OAI

import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionContinuity

namespace OAI

/-! Finite square bounds for the actual convolution of any bounded L2
input, including the localized bounded functions used in the Carleson proof. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem lineConvolution_frame {ι : Type*} (I : Finset ι)
    (q : ι → SchwartzMap ℝ ℂ) (W : ι → ℝ) (hW : ∀ i, W i≠0)
    (M : ℝ) (hM : ∀ eta, (∑ i∈I, ‖q i (W i*eta)‖^2)≤M)
    (f : ℝ → ℂ) (hfm : Measurable f) (hf : MemLp f 2 volume)
    (B : ℝ) (hB : ∀ x, ‖f x‖≤B) :
    (∑ i∈I, ∫ x, ‖lineConvolution (lineProjectionKernel (q i) (W i) (hW i)) f x‖^2)≤
      M*∫ x, ‖f x‖^2 := by
  have h := lineL2Projection_frame I q W hW M hM (hf.toLp f)
  have heq (i : ι) : ‖lineL2Projection (q i) (W i) (hW i) (hf.toLp f)‖^2=
      ∫ x, ‖lineConvolution (lineProjectionKernel (q i) (W i) (hW i)) f x‖^2 := by
    rw [lineL2Projection_on_bounded (q i) (W i) (hW i) f hfm hf B hB]
    exact memLp_toL2_norm_sq volume _ _
  rw [memLp_toL2_norm_sq volume f hf] at h
  simpa only [heq] using h

theorem bounded_indicator_memLp (f : ℝ → ℂ) (hfm : Measurable f)
    (S : Set ℝ) (hS : MeasurableSet S) (hSf : volume S≠⊤)
    (B : ℝ) (hB : ∀ x, ‖f x‖≤B) : MemLp (S.indicator f) 2 volume := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSf
  rw [memLp_indicator_iff_restrict hS]
  exact MemLp.of_bound hfm.aestronglyMeasurable.restrict B
    (Filter.Eventually.of_forall hB)

theorem lineConvolution_local_frame {ι : Type*} (I : Finset ι)
    (q : ι → SchwartzMap ℝ ℂ) (W : ι → ℝ) (hW : ∀ i, W i≠0)
    (M : ℝ) (hMnonneg : 0≤M) (hM : ∀ eta, (∑ i∈I, ‖q i (W i*eta)‖^2)≤M)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B)
    (S : Set ℝ) (hS : MeasurableSet S) (hSf : volume S≠⊤) :
    (∑ i∈I, ∫ x, ‖lineConvolution (lineProjectionKernel (q i) (W i) (hW i)) (S.indicator f) x‖^2)≤
      M*(B^2*volume.real S) := by
  have hf := bounded_indicator_memLp f hfm S hS hSf B hfb
  have hb (x : ℝ) : ‖S.indicator f x‖≤B := by
    by_cases hx : x∈S
    · simpa only [Set.indicator_of_mem hx] using hfb x
    · simp only [Set.indicator_of_notMem hx,norm_zero]
      exact hB
  apply (lineConvolution_frame I q W hW M hM (S.indicator f) (hfm.indicator hS) hf B hb).trans
  apply mul_le_mul_of_nonneg_left _ hMnonneg
  have heq : (fun x => ‖S.indicator f x‖^2)=S.indicator (fun x => ‖f x‖^2) := by
    funext x
    by_cases hx : x∈S <;> simp [hx]
  have hint := hf.integrable_norm_pow (by decide : 2≠0)
  rw [heq,integrable_indicator_iff hS] at hint
  rw [heq,integral_indicator hS]
  calc
    _ ≤ ∫ _x in S, B^2 := integral_mono
      hint
      (integrableOn_const hSf) (fun x => pow_le_pow_left₀ (norm_nonneg _) (hfb x) 2)
    _ = _ := by rw [setIntegral_const,smul_eq_mul,mul_comm]

end LipschitzHilbert.PacketRepresentation

end

end OAI

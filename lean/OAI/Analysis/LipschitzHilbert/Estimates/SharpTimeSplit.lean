import OAI.Analysis.LipschitzHilbert.Fourier.KernelPairing
import OAI.Analysis.LipschitzHilbert.Estimates.SharpTimeMoment

namespace OAI

/-! Exact splitting of sharp time truncations; the two boundary points
are removed only by a null-set argument. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem sharpTimeKernel_split_ae (r s R : ℝ) (hrs : r≤s) (hsR : s≤R) :
    (sharpTimeKernel r R)=ᵐ[volume] fun t => sharpTimeKernel r s t+sharpTimeKernel s R t := by
  have hs : ∀ᵐ t : ℝ, t≠s := by apply ae_iff.mpr; simp
  have hns : ∀ᵐ t : ℝ, t≠ -s := by apply ae_iff.mpr; simp
  filter_upwards [hs,hns] with t ht hnt
  have hn : |t|≠s := by
    intro h
    by_cases hz : 0≤t
    · exact ht (by simpa only [abs_of_nonneg hz] using h)
    · exact hnt (by rw [abs_of_neg (lt_of_not_ge hz)] at h; linarith)
  by_cases h1 : r< |t|
  · by_cases h2 : |t|<s
    · have h3 : |t|<R := h2.trans_le hsR
      have h4 : ¬s< |t| := by linarith
      simp only [sharpTimeKernel,h1,h2,h3,h4,and_self,false_and,
        ite_true,ite_false,add_zero]
    · have h3 : s< |t| := lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm hn)
      by_cases h4 : |t|<R
      · simp only [sharpTimeKernel,h1,h2,h3,h4,and_self,and_false,
          ite_true,ite_false,zero_add]
      · simp only [sharpTimeKernel,h2,h4,and_false,ite_false,add_zero]
  · have h2 : ¬s< |t| := by linarith
    simp only [sharpTimeKernel,h1,h2,false_and,ite_false,add_zero]

theorem kernelPairing_sharp_split (r s R : ℝ) (hr : 0<r) (hrs : r≤s) (hsR : s≤R)
    (u : (ℝ×ℝ) → ℝ) (hu : Measurable u) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    kernelPairing (sharpTimeKernel r R) u f g=
      kernelPairing (sharpTimeKernel r s) u f g+kernelPairing (sharpTimeKernel s R) u f g := by
  have hs : 0<s := hr.trans_le hrs
  have hR : 0<R := hs.trans_le hsR
  have heq : kernelPairing (sharpTimeKernel r R) u f g=
      kernelPairing (fun t => sharpTimeKernel r s t+sharpTimeKernel s R t) u f g := by
    unfold kernelPairing
    apply integral_congr_ae
    filter_upwards [] with z
    congr 1
    unfold slopeKernelOperator
    apply integral_congr_ae
    filter_upwards [sharpTimeKernel_split_ae r s R hrs hsR] with t ht
    rw [ht]
  rw [heq]
  exact kernelPairing_add _ _ (sharpTimeKernel_measurable r s) (sharpTimeKernel_measurable s R)
    (sharpTimeKernel_integrable r s hr hs) (sharpTimeKernel_integrable s R hs hR) u hu f g

end LipschitzHilbert.PacketRepresentation

end

end OAI

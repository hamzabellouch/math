import OAI.Analysis.LipschitzHilbert.Fourier.FrequencyKernelTranslations
import OAI.Analysis.LipschitzHilbert.Estimates.UniformTranslatedProfileBounds

namespace OAI

/-! In the packet coordinates the two Fourier modulations are just
weighted translations of the unmodulated profile. The vertical carrier
phase cancels exactly. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

theorem packetCoordinates_symm_apply (l W theta : ℝ) (hl : l≠0) (hW : W≠0)
    (z : ℝ×ℝ) : (packetCoordinates l W theta hl hW).symm z=
      (l*z.1,W*z.2+theta*(l*z.1)) := rfl

theorem weightedTranslatedProfile_apply (F : SchwartzMap (ℝ×ℝ) ℂ)
    (q : ℕ) (nu : SymbolSpace) (a x : ℝ×ℝ) :
    weightedTranslatedProfile F q nu a x=(symbolWeight q nu:ℂ)*F (x-a) := by
  rw [weightedTranslatedProfile, smul_apply, SchwartzMap.compSubConstCLM_apply]
  rfl

theorem horizontalFrequencyProfile_eq (A : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) :
    convolutionProfile (horizontalFrequencyKernel A nu q l theta) l W theta carrier hl hW=
      weightedTranslatedProfile
        (convolutionProfile (planarInverseSchwartz A) l W theta carrier hl hW)
          q nu (-nu 0,0) := by
  ext z
  rw [weightedTranslatedProfile_apply, convolutionProfile_apply,
    horizontalFrequencyKernel_apply, convolutionProfile_apply]
  have harg : (packetCoordinates l W theta hl hW).symm z+(nu 0*l,nu 0*l*theta)=
      (packetCoordinates l W theta hl hW).symm (z-(-nu 0,0)) := by
    rw [packetCoordinates_symm_apply, packetCoordinates_symm_apply]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [harg]
  simp only [Prod.snd_sub, sub_zero]
  ring

theorem verticalFrequencyProfile_eq (B : SchwartzMap (ℝ×ℝ) ℂ) (nu : SymbolSpace)
    (q : ℕ) (l W theta center : ℝ) (hl : l≠0) (hW : W≠0) :
    convolutionProfile (verticalFrequencyKernel B nu q W center)
        l W theta (2*Real.pi*center) hl hW=
      weightedTranslatedProfile
        (convolutionProfile (planarInverseSchwartz B) l W theta (2*Real.pi*center) hl hW)
          q nu (0,-nu 1) := by
  ext z
  rw [weightedTranslatedProfile_apply, convolutionProfile_apply,
    verticalFrequencyKernel_apply, convolutionProfile_apply]
  have harg : (packetCoordinates l W theta hl hW).symm z+(0,nu 1*W)=
      (packetCoordinates l W theta hl hW).symm (z-(0,-nu 1)) := by
    rw [packetCoordinates_symm_apply, packetCoordinates_symm_apply]
    ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> ring
  rw [harg]
  simp only [Prod.snd_sub, sub_neg_eq_add]
  have hphase :
      Complex.exp (((-(2*Real.pi*center*W)*z.2:ℝ):ℂ)*Complex.I)*
        (Real.fourierChar (-(nu 1*W*center)):ℂ)=
      Complex.exp (((-(2*Real.pi*center*W)*(z.2+nu 1):ℝ):ℂ)*Complex.I) := by
    rw [Real.fourierChar_apply, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (symbolWeight q nu:ℂ)*(l*W:ℂ)*
      (Complex.exp (((-(2*Real.pi*center*W)*z.2:ℝ):ℂ)*Complex.I)*
        (Real.fourierChar (-(nu 1*W*center)):ℂ))*
          planarInverseSchwartz B ((packetCoordinates l W theta hl hW).symm (z-(0,-nu 1))) := by ring
    _ = _ := by rw [hphase]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI

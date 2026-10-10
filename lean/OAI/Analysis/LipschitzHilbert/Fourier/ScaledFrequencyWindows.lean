import OAI.Analysis.LipschitzHilbert.Fourier.FrequencyProfileNormalization

namespace OAI

/-! Frequency windows obtained from a fixed normalized packet profile.
The normalization is exact and removes all spatial scale parameters. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def normalizedSpatialKernel (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) : SchwartzMap (ℝ×ℝ) ℂ :=
  ((l*W:ℂ)⁻¹) • physicalPlanarPacket F 0 0 l W theta carrier hl hW

def scaledFrequencyWindow (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) : SchwartzMap (ℝ×ℝ) ℂ :=
  planarFourierSchwartz (normalizedSpatialKernel F l W theta carrier hl hW)

theorem scaledFrequencyWindow_inverse (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) :
    planarInverseSchwartz (scaledFrequencyWindow F l W theta carrier hl hW)=
      normalizedSpatialKernel F l W theta carrier hl hW := by
  ext x
  rw [planarInverseSchwartz_apply]
  have he : (scaledFrequencyWindow F l W theta carrier hl hW : ℝ×ℝ → ℂ)=
      planarFourier (normalizedSpatialKernel F l W theta carrier hl hW) :=
    funext (planarFourierSchwartz_apply _)
  rw [he]
  exact planarFourier_inversion _ x

theorem normalizedSpatialKernel_profile (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) :
    convolutionProfile (normalizedSpatialKernel F l W theta carrier hl hW)
      l W theta carrier hl hW=F := by
  ext z
  rw [convolutionProfile_apply]
  simp only [normalizedSpatialKernel, smul_apply, smul_eq_mul]
  rw [physicalPlanarPacket_apply, packetCoordinates_symm_apply]
  simp only [sub_zero]
  have hy : (W*z.2+theta*(l*z.1))-theta*(l*z.1)=W*z.2 := by ring
  rw [hy]
  have hz1 : l*z.1/l=z.1 := by field_simp
  have hz2 : W*z.2/W=z.2 := by field_simp
  rw [hz1,hz2]
  have he : Complex.exp (((-(carrier*W)*z.2:ℝ):ℂ)*Complex.I)*
      Complex.exp (((carrier*(W*z.2):ℝ):ℂ)*Complex.I)=1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast
    ring
  have harea : (l*W:ℂ)≠0 := by exact_mod_cast mul_ne_zero hl hW
  calc
    _ = ((l*W:ℂ)*(l*W:ℂ)⁻¹)*
        (Complex.exp (((-(carrier*W)*z.2:ℝ):ℂ)*Complex.I)*
          Complex.exp (((carrier*(W*z.2):ℝ):ℂ)*Complex.I))*F z := by ring
    _ = F z := by rw [mul_inv_cancel₀ harea, he, one_mul, one_mul]

theorem scaledFrequencyWindow_profile (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) :
    convolutionProfile (planarInverseSchwartz (scaledFrequencyWindow F l W theta carrier hl hW))
      l W theta carrier hl hW=F := by
  rw [scaledFrequencyWindow_inverse, normalizedSpatialKernel_profile]

theorem scaled_horizontal_profile_bound (F : SchwartzMap (ℝ×ℝ) ℂ) (n : ℕ) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace,
      ∀ l W theta carrier : ℝ, ∀ hl : l≠0, ∀ hW : W≠0,
      planarProfileConstant (convolutionProfile
        (horizontalFrequencyKernel (scaledFrequencyWindow F l W theta carrier hl hW) nu q l theta)
          l W theta carrier hl hW) n≤C := by
  obtain ⟨q₀,C,hC,hbound⟩ := uniform_translated_profile_bound F n
  refine ⟨q₀,C,hC,?_⟩
  intro q hq nu l W theta carrier hl hW
  rw [horizontalFrequencyProfile_eq, scaledFrequencyWindow_profile]
  apply hbound q hq nu (-nu 0,0)
  simpa only [Prod.norm_def, norm_neg, norm_zero, max_eq_left (norm_nonneg _)] using PiLp.norm_apply_le nu 0

theorem scaled_vertical_profile_bound (F : SchwartzMap (ℝ×ℝ) ℂ) (n : ℕ) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace,
      ∀ l W theta center : ℝ, ∀ hl : l≠0, ∀ hW : W≠0,
      planarProfileConstant (convolutionProfile
        (verticalFrequencyKernel (scaledFrequencyWindow F l W theta (2*Real.pi*center) hl hW)
          nu q W center) l W theta (2*Real.pi*center) hl hW) n≤C := by
  obtain ⟨q₀,C,hC,hbound⟩ := uniform_translated_profile_bound F n
  refine ⟨q₀,C,hC,?_⟩
  intro q hq nu l W theta center hl hW
  rw [verticalFrequencyProfile_eq, scaledFrequencyWindow_profile]
  apply hbound q hq nu (0,-nu 1)
  simpa only [Prod.norm_def, norm_neg, norm_zero, max_eq_right (norm_nonneg _)] using PiLp.norm_apply_le nu 1

end LipschitzHilbert.PacketRepresentation

end

end OAI

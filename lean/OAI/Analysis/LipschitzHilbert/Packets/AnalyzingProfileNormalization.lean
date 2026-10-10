import OAI.Analysis.LipschitzHilbert.Fourier.ScaledFrequencyWindows

namespace OAI

/-! The analyzing wave uses reflection and conjugation together. Its
positive carrier is unchanged, and its normalized profile has the same
uniform weighted-translation bounds as the synthesizing profile. -/
noncomputable section
open scoped ComplexConjugate
namespace LipschitzHilbert.PacketRepresentation

def reflectedConjugateProfile (F : SchwartzMap (ℝ×ℝ) ℂ) : SchwartzMap (ℝ×ℝ) ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearIsometryEquiv.neg ℝ (E := ℝ×ℝ)) F).postcompCLM Complex.conjCLE.toContinuousLinearMap

theorem reflectedConjugateProfile_apply (F : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    reflectedConjugateProfile F z=conj (F (-z)) := rfl

theorem reflectedConjugateProfile_weightedTranslate (F : SchwartzMap (ℝ×ℝ) ℂ)
    (q : ℕ) (nu : SymbolSpace) (a : ℝ×ℝ) :
    reflectedConjugateProfile (weightedTranslatedProfile F q nu a)=
      weightedTranslatedProfile (reflectedConjugateProfile F) q nu (-a) := by
  ext z
  simp only [reflectedConjugateProfile_apply, weightedTranslatedProfile_apply,
    map_mul, Complex.conj_ofReal]
  congr 2
  abel_nf

theorem physical_reflectedConjugateProfile (F : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) (z x : ℝ×ℝ) :
    physicalPlanarPacket (reflectedConjugateProfile F) z.1 z.2 l W theta carrier hl hW x=
      conj (physicalPlanarPacket F 0 0 l W theta carrier hl hW (z-x)) := by
  rw [physicalPlanarPacket_apply, reflectedConjugateProfile_apply, physicalPlanarPacket_apply,
    map_mul, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Prod.fst_sub, Prod.snd_sub, sub_zero]
  have harg : -((x.1-z.1)/l,((x.2-z.2)-theta*(x.1-z.1))/W)=
      ((z.1-x.1)/l,((z.2-x.2)-theta*(z.1-x.1))/W) := by
    ext <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring
  rw [harg]
  congr 2
  push_cast
  ring

theorem physical_analyzing_packet (K : SchwartzMap (ℝ×ℝ) ℂ)
    (l W theta carrier : ℝ) (hl : l≠0) (hW : W≠0) (z x : ℝ×ℝ) :
    physicalPlanarPacket
      (reflectedConjugateProfile (convolutionProfile K l W theta carrier hl hW))
        z.1 z.2 l W theta carrier hl hW x=analyzingWave (l*W) K z x := by
  rw [physical_reflectedConjugateProfile,
    physical_convolution_packet K l W theta carrier hl hW (0,0) (z-x)]
  simp only [synthesisWave, analyzingWave, show (0,0)=(0:ℝ×ℝ) from rfl,
    sub_zero, map_mul, Complex.conj_ofReal]

theorem scaled_analyzing_profile_bound (F : SchwartzMap (ℝ×ℝ) ℂ) (n : ℕ) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace,
      ∀ l W theta center : ℝ, ∀ hl : l≠0, ∀ hW : W≠0,
      planarProfileConstant (reflectedConjugateProfile (convolutionProfile
        (verticalFrequencyKernel (scaledFrequencyWindow F l W theta (2*Real.pi*center) hl hW)
          nu q W center) l W theta (2*Real.pi*center) hl hW)) n≤C := by
  obtain ⟨q₀,C,hC,hbound⟩ := uniform_translated_profile_bound (reflectedConjugateProfile F) n
  refine ⟨q₀,C,hC,?_⟩
  intro q hq nu l W theta center hl hW
  rw [verticalFrequencyProfile_eq, scaledFrequencyWindow_profile,
    reflectedConjugateProfile_weightedTranslate]
  apply hbound q hq nu (-(0,-nu 1))
  simpa only [norm_neg, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using PiLp.norm_apply_le nu 1

end LipschitzHilbert.PacketRepresentation

end

end OAI

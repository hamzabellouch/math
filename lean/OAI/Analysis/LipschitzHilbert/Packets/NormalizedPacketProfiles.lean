import OAI.Analysis.LipschitzHilbert.Packets.AnalyzingProfileNormalization

namespace OAI

/-! A single Fourier parameter determines both normalized wave profiles.
Their common bound is chosen before all spatial scales and frequency bins. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def synthesisProfile (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace) :
    SchwartzMap (ℝ×ℝ) ℂ := weightedTranslatedProfile F q nu (-nu 0,0)

def analysisProfile (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace) :
    SchwartzMap (ℝ×ℝ) ℂ :=
  weightedTranslatedProfile (reflectedConjugateProfile F) q nu (0,nu 1)

theorem synthesisProfile_eq (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (l W theta center : ℝ) (hl : l≠0) (hW : W≠0) :
    synthesisProfile F q nu = convolutionProfile
      (horizontalFrequencyKernel
        (scaledFrequencyWindow F l W theta (2*Real.pi*center) hl hW) nu q l theta)
      l W theta (2*Real.pi*center) hl hW := by
  rw [horizontalFrequencyProfile_eq, scaledFrequencyWindow_profile]
  rfl

theorem analysisProfile_eq (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (l W theta center : ℝ) (hl : l≠0) (hW : W≠0) :
    analysisProfile F q nu = reflectedConjugateProfile (convolutionProfile
      (verticalFrequencyKernel
        (scaledFrequencyWindow F l W theta (2*Real.pi*center) hl hW) nu q W center)
      l W theta (2*Real.pi*center) hl hW) := by
  rw [verticalFrequencyProfile_eq, scaledFrequencyWindow_profile,
    reflectedConjugateProfile_weightedTranslate]
  simp only [analysisProfile, Prod.neg_mk, neg_zero, neg_neg]

theorem uniform_normalized_profile_pair (F G : SchwartzMap (ℝ×ℝ) ℂ) (n : ℕ) :
    ∃ q₀ : ℕ, ∃ C : ℝ, 0<C ∧ ∀ q : ℕ, q₀≤q → ∀ nu : SymbolSpace,
      planarProfileConstant (synthesisProfile F q nu) n ≤ C ∧
        planarProfileConstant (analysisProfile G q nu) n ≤ C := by
  obtain ⟨qF,CF,hCF,hF⟩ := uniform_translated_profile_bound F n
  obtain ⟨qG,CG,hCG,hG⟩ := uniform_translated_profile_bound (reflectedConjugateProfile G) n
  refine ⟨max qF qG,max CF CG,lt_max_of_lt_left hCF,?_⟩
  intro q hq nu
  constructor
  · apply (hF q ((le_max_left _ _).trans hq) nu (-nu 0,0) ?_).trans (le_max_left _ _)
    simpa only [Prod.norm_def, norm_neg, norm_zero, max_eq_left (norm_nonneg _)] using
      PiLp.norm_apply_le nu 0
  · apply (hG q ((le_max_right _ _).trans hq) nu (0,nu 1) ?_).trans (le_max_right _ _)
    simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using
      PiLp.norm_apply_le nu 1

theorem physical_synthesisProfile (F : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (l W theta center : ℝ) (hl : l≠0) (hW : W≠0) (z x : ℝ×ℝ) :
    physicalPlanarPacket (synthesisProfile F q nu) z.1 z.2
      l W theta (2*Real.pi*center) hl hW x =
    synthesisWave (l*W) (horizontalFrequencyKernel
      (scaledFrequencyWindow F l W theta (2*Real.pi*center) hl hW) nu q l theta) z x := by
  rw [synthesisProfile_eq F q nu l W theta center hl hW,
    physical_convolution_packet]

theorem physical_analysisProfile (G : SchwartzMap (ℝ×ℝ) ℂ) (q : ℕ) (nu : SymbolSpace)
    (l W theta center : ℝ) (hl : l≠0) (hW : W≠0) (z x : ℝ×ℝ) :
    physicalPlanarPacket (analysisProfile G q nu) z.1 z.2
      l W theta (2*Real.pi*center) hl hW x =
    analyzingWave (l*W) (verticalFrequencyKernel
      (scaledFrequencyWindow G l W theta (2*Real.pi*center) hl hW) nu q W center) z x := by
  rw [analysisProfile_eq G q nu l W theta center hl hW,
    physical_analyzing_packet]

end LipschitzHilbert.PacketRepresentation

end

end OAI

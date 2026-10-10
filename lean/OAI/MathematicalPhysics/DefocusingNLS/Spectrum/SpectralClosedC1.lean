import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralClosedFluxPrimitive

namespace OAI

/-! A classical derivative continuous up to the endpoints gives a C¹ extension. -/

open Set
namespace DefocusingNLS

theorem spectralClosedC1_extension (a b : ℝ) (hab : a < b) (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) :
    ∃ u : ℝ → ℂ, Continuous u ∧
      (∀ x ∈ Icc a b, HasDerivAt u (g x) x) ∧ EqOn u f (Icc a b) := by
  obtain ⟨u,hu,hdu,he⟩ := spectralClosedFlux_primitive a b hab f g hg hd
  refine ⟨u,hu,hdu,?_⟩
  apply he.symm.of_subset_closure hu.continuousOn hf Ioo_subset_Icc_self
  rw [closure_Ioo hab.ne]

end DefocusingNLS

end OAI

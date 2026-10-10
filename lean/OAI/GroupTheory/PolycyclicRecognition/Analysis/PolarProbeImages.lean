import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarTiledChains

namespace OAI

/-! # Centering the translated probes removes the contact-pivot parameter -/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- The target template used by the measured path restriction is independent
of the inward displacement of the source pivot. -/
theorem centered_polar_probe_image
    (K : ProperCone ℝ (StrongDual ℝ W)) (ε : ℝ) (w : W)
    (A : W →ₗ[ℝ] V) (k : Fin 3) :
    (fun z => A (z - w)) '' polarSamplingTemplates K ε w k =
      A '' normalizedPolarTemplates K ε k := by
  ext y
  constructor
  · rintro ⟨z, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u + w, ⟨u, hu, rfl⟩, by simp⟩

end PolycyclicRecognition

end

end OAI

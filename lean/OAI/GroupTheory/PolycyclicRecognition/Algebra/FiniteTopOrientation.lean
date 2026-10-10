import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PoincareTopHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteIntegralHomology

namespace OAI

/-! # A finite nonzero top orientation homology group -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem IsIntegralPoincareDualityGroup.exists_finite_nonzero_top {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) :
    ∃ D : Rep ℤ G, Nonempty (D.V ≃ₗ[ℤ] ℤ) ∧
      Module.Finite ℤ (groupHomology D n) ∧ ∃ x : groupHomology D n, x ≠ 0 := by
  obtain ⟨D, ⟨eD⟩, hD⟩ := hG.topHomology_orientation
  have hfiniteD : Module.Finite ℤ D := Module.Finite.equiv eD.symm
  let := hfiniteD
  refine ⟨D, ⟨eD⟩, (hG.typeFPInfinity G n).homology_finite D, ?_⟩
  obtain ⟨e⟩ := hD D
  refine ⟨e.symm (𝟙 D), ?_⟩
  intro hx
  have hid : (𝟙 D : D ⟶ D) = 0 := by
    have h := congrArg e hx
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using h
  have hv := congrArg (fun f : D ⟶ D => eD (f.hom (eD.symm 1))) hid
  simp at hv

end PolycyclicRecognition

end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PoincareTopHomology

namespace OAI

/-! # Detecting Poincare dimension with homology coefficients -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem IsIntegralPoincareDualityGroup.homologicalDimension_le {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) (d : ℕ)
    (hvanish : ∀ A : Rep ℤ G, ∀ i, d < i → IsZero (groupHomology A i)) : n ≤ d := by
  by_contra hn
  have hdn : d < n := Nat.lt_of_not_ge hn
  obtain ⟨D, ⟨eD⟩, he⟩ := hG.topHomology_orientation
  obtain ⟨eH⟩ := he D
  let := ModuleCat.subsingleton_of_isZero (hvanish D n hdn)
  have hid : (𝟙 D : D ⟶ D) = 0 := by
    apply eH.symm.injective
    exact Subsingleton.elim _ _
  have hv := congrArg (fun f : D ⟶ D => f.hom (eD.symm 1)) hid
  change eD.symm 1 = 0 at hv
  have h10 : (1 : ℤ) = 0 := by
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg eD hv
  exact one_ne_zero h10

end PolycyclicRecognition

end

end OAI

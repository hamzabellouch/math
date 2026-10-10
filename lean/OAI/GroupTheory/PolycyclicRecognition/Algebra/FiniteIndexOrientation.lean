import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.PoincareTopHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteIndexFiniteness
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
import Mathlib.RepresentationTheory.FiniteIndex

namespace OAI

/-! # Compatibility of top-homology orientations at finite index

A nonzero intertwiner between integral rank-one representations determines
their isomorphism. Shapiro and finite-index induction/coinduction produce
that intertwiner without choosing fundamental classes.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G]

theorem topHomology_orientation_restrict (H : Subgroup G) [H.FiniteIndex] (n : ℕ)
    (D : Rep ℤ G) (E : Rep ℤ H)
    (eD : D.V ≃ₗ[ℤ] ℤ) (eE : E.V ≃ₗ[ℤ] ℤ)
    (hD : ∀ A : Rep ℤ G, Nonempty (groupHomology A n ≃ₗ[ℤ] (D ⟶ A)))
    (hE : ∀ A : Rep ℤ H, Nonempty (groupHomology A n ≃ₗ[ℤ] (E ⟶ A))) :
    Nonempty (Rep.res H.subtype D ≅ E) := by
  classical
  obtain ⟨d⟩ := hD (Rep.ind H.subtype E)
  obtain ⟨e⟩ := hE E
  let a : (D ⟶ Rep.ind H.subtype E) ≃ₗ[ℤ] (Rep.res H.subtype D ⟶ E) :=
    (Linear.homCongr ℤ (Iso.refl D) (Rep.indCoindIso E)).trans
      (Rep.resCoindHomEquiv.{0} H.subtype D E).symm
  let b := a.symm.trans (d.symm.trans
    ((groupHomology.indIso H E n).toLinearEquiv.trans e))
  have hid : (𝟙 E : E ⟶ E) ≠ 0 := by
    intro h
    have hv := congrArg (fun f : E ⟶ E => f.hom (eE.symm 1)) h
    change eE.symm 1 = 0 at hv
    exact (show (1 : ℤ) ≠ 0 from one_ne_zero) (by simpa using congrArg eE hv)
  have hf : b.symm (𝟙 E) ≠ 0 := by
    intro h
    apply hid
    have he := congrArg b h
    simpa using he
  exact rankOne_rep_iso_of_nonzero (Rep.res H.subtype D) E eD eE (b.symm (𝟙 E)) hf

theorem IsIntegralPoincareDualityGroup.topHomology_orientation_finiteIndex {n : ℕ}
    (hG : IsIntegralPoincareDualityGroup G n) :
    ∃ D : Rep ℤ G, Nonempty (D.V ≃ₗ[ℤ] ℤ) ∧
      ∀ (H : Subgroup G) (_ : H.FiniteIndex) (A : Rep ℤ H),
        Nonempty (groupHomology A n ≃ₗ[ℤ] (Rep.res H.subtype D ⟶ A)) := by
  obtain ⟨D, ⟨eD⟩, hD⟩ := hG.topHomology_orientation
  refine ⟨D, ⟨eD⟩, ?_⟩
  intro H hH A
  let := hH
  obtain ⟨E, ⟨eE⟩, hE⟩ := (hG.finiteIndex_subgroup H).topHomology_orientation
  obtain ⟨i⟩ := topHomology_orientation_restrict H n D E eD eE hD hE
  obtain ⟨eA⟩ := hE A
  exact ⟨eA.trans (Linear.homCongr ℤ i.symm (Iso.refl A))⟩

end PolycyclicRecognition

end

end OAI

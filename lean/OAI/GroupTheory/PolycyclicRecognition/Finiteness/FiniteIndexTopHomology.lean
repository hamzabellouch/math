import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteIndexTrace
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.TopHomologyNaturality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneEndomorphisms

namespace OAI

/-! # The index on top homology with induced orientation coefficients

The coefficient return map becomes multiplication by the subgroup index.
Identifying it with subgroup inclusion is a separate bar-resolution step.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] (D : Rep ℤ G)

def finiteIndexOrientationHomEquiv :
    (D ⟶ Rep.ind H.subtype (Rep.res H.subtype D)) ≃ₗ[ℤ]
      (Rep.res H.subtype D ⟶ Rep.res H.subtype D) := by
  classical
  exact (Linear.homCongr ℤ (Iso.refl D) (Rep.indCoindIso (Rep.res H.subtype D))).trans
    (Rep.resCoindHomEquiv.{0} H.subtype D (Rep.res H.subtype D)).symm

theorem finiteIndexOrientationHomEquiv_symm_id :
    (finiteIndexOrientationHomEquiv H D).symm (𝟙 _) = finiteIndexLift H D := by
  classical
  simp [finiteIndexOrientationHomEquiv, Linear.homCongr, finiteIndexLift]

theorem finiteIndexOrientationHom_return (eD : D.V ≃ₗ[ℤ] ℤ)
    (f : D ⟶ Rep.ind H.subtype (Rep.res H.subtype D)) :
    f ≫ finiteIndexReturn H D =
      ((rankOneEndomorphismsEquiv (Rep.res H.subtype D) eD)
        (finiteIndexOrientationHomEquiv H D f) * (H.index : ℤ)) • (𝟙 D : D ⟶ D) := by
  let z := (rankOneEndomorphismsEquiv (Rep.res H.subtype D) eD)
    (finiteIndexOrientationHomEquiv H D f)
  have ha : finiteIndexOrientationHomEquiv H D f = z • (𝟙 _) :=
    (rankOneEndomorphismsEquiv (Rep.res H.subtype D) eD).symm_apply_apply _ |>.symm
  have hf : f = z • finiteIndexLift H D := by
    apply (finiteIndexOrientationHomEquiv H D).injective
    rw [map_zsmul]
    rw [← finiteIndexOrientationHomEquiv_symm_id, LinearEquiv.apply_symm_apply]
    exact ha
  change f ≫ finiteIndexReturn H D = (z * (H.index : ℤ)) • (𝟙 D : D ⟶ D)
  rw [hf, Preadditive.zsmul_comp, finiteIndexLift_return]
  rw [← natCast_zsmul, smul_smul]

theorem finiteIndex_topHomology_return {n : ℕ} (eD : D.V ≃ₗ[ℤ] ℤ)
    (e : ∀ A : Rep ℤ G, groupHomology A n ≃ₗ[ℤ] (D ⟶ A))
    (he : ∀ (A B : Rep ℤ G) (f : A ⟶ B) (x : groupHomology A n),
      e B (groupHomology.map (MonoidHom.id G) f n x) = e A x ≫ f) :
    ∃ (u : groupHomology (Rep.ind H.subtype (Rep.res H.subtype D)) n ≃ₗ[ℤ] ℤ)
      (v : groupHomology D n ≃ₗ[ℤ] ℤ),
      ∀ x, v (groupHomology.map (MonoidHom.id G) (finiteIndexReturn H D) n x) =
        (H.index : ℤ) * u x := by
  let u := (e _).trans ((finiteIndexOrientationHomEquiv H D).trans
    (rankOneEndomorphismsEquiv (Rep.res H.subtype D) eD))
  let v := (e D).trans (rankOneEndomorphismsEquiv D eD)
  refine ⟨u, v, ?_⟩
  intro x
  change rankOneEndomorphismsEquiv D eD
    (e D (groupHomology.map (MonoidHom.id G) (finiteIndexReturn H D) n x)) = _
  rw [he, finiteIndexOrientationHom_return H D eD, map_zsmul]
  change (_ * (H.index : ℤ)) * (rankOneEndomorphismsEquiv D eD (𝟙 D)) = _
  simp [rankOneEndomorphismsEquiv, u, mul_comm]

end PolycyclicRecognition

end

end OAI

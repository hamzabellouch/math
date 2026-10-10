import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalOrientationCoefficient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalTensorNaturality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalCharacterCancellation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.OrientationHomologyAction
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalHomologyAction

namespace OAI

/-! # Cancelling conjugation on rational top homology -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory MonoidalCategory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem rationalOrientation_conjugation_naturality (R : Rep ℤ N)
    (eR : R.V ≃ₗ[ℤ] ℤ) (χ : G →* ℚ)
    (hχ : ∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ))
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)
    (d : ℕ) (g : G) :
    groupHomology.map (MonoidHom.id N) (rationalizedOrientationIso N R eR χ hχ).hom d ≫
        normalHomologyMap ℤ N (rationalCharacterRep χ) d g =
      groupHomology.map (MulAut.conjNormal (H := N) g).toMonoidHom
          (trivialTensorCoefficientMap (rationalScalarMap (χ g)) _
            (invariantConjugationCoefficient N R hinv g)) d ≫
        groupHomology.map (MonoidHom.id N) (rationalizedOrientationIso N R eR χ hχ).hom d := by
  rw [normalHomologyMap, ← groupHomology.map_comp, ← groupHomology.map_comp]
  apply groupHomology.map_congr rfl
  apply TensorProduct.ext
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro v
  change χ g * rationalizedOrientationEquiv R eR (q ⊗ₜ[ℤ] v) =
    rationalizedOrientationEquiv R eR ((χ g * q) ⊗ₜ[ℤ] v)
  rw [rationalizedOrientationEquiv_tmul, rationalizedOrientationEquiv_tmul]
  ring

theorem rationalOrientationHomology_trivial (R : Rep ℤ N)
    (eR : R.V ≃ₗ[ℤ] ℤ) (χ : G →* ℚ)
    (hχ : ∀ a : N, χ (a : G) = (rankOneCharacter R eR a : ℚ))
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)
    (d : ℕ) (e : (ℚ ⊗[ℤ] (groupHomology R d)) ≃ₗ[ℚ] ℚ)
    (hc : ∀ g, χ g * rationalActionCharacter
      (invariantConjugationHomologyAction N R hinv d) e g = 1) (g : G) :
    normalHomologyMap ℤ N (rationalCharacterRep χ) d g = 𝟙 _ := by
  classical
  let f := (MulAut.conjNormal (H := N) g).toMonoidHom
  let φ := invariantConjugationCoefficient N R hinv g
  let ψ := trivialTensorCoefficientMap (rationalScalarMap (χ g)) f φ
  let I := rationalTensorHomologyIso R d
  have ht : (tensorLeft (ModuleCat.of ℤ ℚ)).map (groupHomology.map f φ d) ≫
      (((curriedTensor (ModuleCat ℤ)).map (rationalScalarMap (χ g))).app
        (groupHomology R d)) = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have he : ((tensorLeft (ModuleCat.of ℤ ℚ)).map (groupHomology.map f φ d) ≫
        (((curriedTensor (ModuleCat ℤ)).map (rationalScalarMap (χ g))).app
          (groupHomology R d))).hom z =
        TensorProduct.map (rationalScalarMap (χ g)).hom
          (integralLinear ((invariantConjugationHomologyAction N R hinv d) g)) z := by
      induction z using TensorProduct.inductionOn with
      | tmul q x => rfl
      | add x y hx hy =>
        simp only [map_add, hx, hy]
    exact he.trans (rationalTensorAction_cancel _ e g _ (hc g) z)
  have hm : groupHomology.map f ψ d = 𝟙 _ := by
    apply (cancel_mono I.hom).mp
    rw [rationalTensorHomologyIso_naturality R R (rationalScalarMap (χ g)) f φ d,
      ht, Category.comp_id, Category.id_comp]
  let J := (groupHomology.functor ℤ N d).mapIso (rationalizedOrientationIso N R eR χ hχ)
  apply (cancel_epi J.hom).mp
  change groupHomology.map (MonoidHom.id N) (rationalizedOrientationIso N R eR χ hχ).hom d ≫
      normalHomologyMap ℤ N (rationalCharacterRep χ) d g = J.hom ≫ 𝟙 _
  rw [rationalOrientation_conjugation_naturality N R eR χ hχ hinv d g, hm]
  simp only [Category.id_comp, Category.comp_id]
  rfl

end PolycyclicRecognition

end

end OAI

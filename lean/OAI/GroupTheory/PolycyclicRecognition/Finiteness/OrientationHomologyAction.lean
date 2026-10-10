import OAI.GroupTheory.PolycyclicRecognition.Algebra.TopOrientationAutomorphisms
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalRankOneAction
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OAI

/-! # Ambient conjugation on the local top orientation homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

theorem orientation_action_invariant (R : Rep ℤ N) (eR : R.V ≃ₗ[ℤ] ℤ) (d : ℕ)
    (x : groupHomology R d) (hx : x ≠ 0)
    (hdetect : ∀ A : Rep ℤ N, Nonempty (A.V ≃ₗ[ℤ] ℤ) →
      (∃ y : groupHomology A d, y ≠ 0) → Nonempty (R ≅ A))
    (g : G) (a : N) : R.ρ (MulAut.conjNormal g a) = R.ρ a := by
  have hc := topOrientation_character_aut R eR d x hx hdetect (MulAut.conjNormal g)
  have he := congrArg (fun c : N →* ℤ => c a) hc
  apply LinearMap.ext
  intro v
  apply eR.injective
  calc
    eR (R.ρ (MulAut.conjNormal g a) v) =
        eR v * (rankOneCharacter R eR (MulAut.conjNormal g a)) :=
      rankOne_action_coordinate R eR _ v
    _ = eR v * (rankOneCharacter R eR a) := congrArg (fun z : ℤ => eR v * z) he
    _ = eR (R.ρ a v) := (rankOne_action_coordinate R eR a v).symm

def invariantConjugationCoefficient (R : Rep ℤ N)
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a) (g : G) :
    R ⟶ Rep.res (MulAut.conjNormal (H := N) g).toMonoidHom R :=
  Rep.ofHom ⟨LinearMap.id, by
    intro a
    change LinearMap.id ∘ₗ R.ρ a = R.ρ (MulAut.conjNormal g a) ∘ₗ LinearMap.id
    rw [hinv, LinearMap.id_comp, LinearMap.comp_id]⟩

def invariantConjugationHomologyMap (R : Rep ℤ N)
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)
    (d : ℕ) (g : G) : groupHomology R d ⟶ groupHomology R d :=
  groupHomology.map (MulAut.conjNormal (H := N) g).toMonoidHom
    (invariantConjugationCoefficient N R hinv g) d

theorem invariantConjugationHomologyMap_one (R : Rep ℤ N)
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a) (d : ℕ) :
    invariantConjugationHomologyMap N R hinv d 1 = 𝟙 _ := by
  rw [invariantConjugationHomologyMap, ← groupHomology.map_id]
  apply groupHomology.map_congr
  · ext a
    exact congrArg (fun e : MulAut N => ((e a : N) : G)) (map_one (MulAut.conjNormal (H := N)))
  · rfl

theorem invariantConjugationHomologyMap_mul (R : Rep ℤ N)
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)
    (d : ℕ) (g h : G) :
    invariantConjugationHomologyMap N R hinv d (g * h) =
      invariantConjugationHomologyMap N R hinv d h ≫
        invariantConjugationHomologyMap N R hinv d g := by
  rw [invariantConjugationHomologyMap, invariantConjugationHomologyMap,
    invariantConjugationHomologyMap, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · ext a
    exact congrArg (fun e : MulAut N => ((e a : N) : G)) (map_mul (MulAut.conjNormal (H := N)) g h)
  · rfl

def invariantConjugationHomologyAction (R : Rep ℤ N)
    (hinv : ∀ (g : G) (a : N), R.ρ (MulAut.conjNormal g a) = R.ρ a)
    (d : ℕ) : G →* AddMonoid.End (groupHomology R d) where
  toFun g := (invariantConjugationHomologyMap N R hinv d g).hom.toAddMonoidHom
  map_one' := by
    rw [invariantConjugationHomologyMap_one]
    rfl
  map_mul' g h := by
    rw [invariantConjugationHomologyMap_mul]
    rfl

end PolycyclicRecognition

end

end OAI

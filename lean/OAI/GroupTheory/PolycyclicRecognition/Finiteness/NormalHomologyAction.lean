import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OAI

/-! # Conjugation on normal-subgroup homology with ambient coefficients -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
attribute [local instance 2000] Rep.hV2
variable (k : Type) [CommRing k] {G : Type} [Group G]
  (N : Subgroup G) [N.Normal] (A : Rep k G)

def normalHomologyCoefficient (g : G) :
    Rep.res N.subtype A ⟶
      Rep.res (MulAut.conjNormal (H := N) g).toMonoidHom (Rep.res N.subtype A) :=
  Rep.ofHom ⟨A.ρ g, by
    intro n
    change A.ρ g ∘ₗ A.ρ (n : G) = A.ρ (g * n * g⁻¹) ∘ₗ A.ρ g
    change A.ρ g * A.ρ (n : G) = A.ρ (g * n * g⁻¹) * A.ρ g
    rw [← map_mul, ← map_mul]
    congr 1
    group⟩

def normalHomologyMap (i : ℕ) (g : G) :
    groupHomology (Rep.res N.subtype A) i ⟶ groupHomology (Rep.res N.subtype A) i :=
  groupHomology.map (MulAut.conjNormal (H := N) g).toMonoidHom
    (normalHomologyCoefficient k N A g) i

theorem normalHomologyMap_one (i : ℕ) : normalHomologyMap k N A i 1 = 𝟙 _ := by
  rw [normalHomologyMap, ← groupHomology.map_id]
  apply groupHomology.map_congr
  · ext n
    exact congrArg (fun e : MulAut N => ((e n : N) : G)) (map_one (MulAut.conjNormal (H := N)))
  · apply LinearMap.ext
    intro x
    change A.ρ 1 x = x
    simp

theorem normalHomologyMap_mul (i : ℕ) (g h : G) :
    normalHomologyMap k N A i (g * h) =
      normalHomologyMap k N A i h ≫ normalHomologyMap k N A i g := by
  rw [normalHomologyMap, normalHomologyMap, normalHomologyMap, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · ext n
    exact congrArg (fun e : MulAut N => ((e n : N) : G)) (map_mul (MulAut.conjNormal (H := N)) g h)
  · apply LinearMap.ext
    intro x
    change A.ρ (g * h) x = A.ρ g (A.ρ h x)
    rw [map_mul, Module.End.mul_apply]

def normalHomologyAction (i : ℕ) : Rep k G :=
  Rep.of { toFun g := (normalHomologyMap k N A i g).hom
           map_one' := by rw [normalHomologyMap_one]; rfl
           map_mul' g h := by rw [normalHomologyMap_mul]; rfl }

end PolycyclicRecognition

end

end OAI

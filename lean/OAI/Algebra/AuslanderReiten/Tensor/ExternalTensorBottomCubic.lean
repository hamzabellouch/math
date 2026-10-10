import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorBottomDifferential

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P U : ChainComplex (ModuleCat.{u} A) ℕ) (Q V : ChainComplex (ModuleCat.{u} B) ℕ)
local notation "E" => A ⊗[k] B

theorem bottomMap_add (s t : ℕ) (f f' : U.X s ⟶ P.X t) (g : V.X 0 ⟶ Q.X 0) :
    bottomMap k A B P Q U V s t (f+f') g =
      bottomMap k A B P Q U V s t f g + bottomMap k A B P Q U V s t f' g := by
  apply LinearMap.ext
  intro x
  have hh := congrArg (fun h => h.hom (bottomProjection k A B U V s x))
    (mapHom_add_left k A B f f' g)
  change map k A B (f+f').hom g.hom _ =
    map k A B f.hom g.hom _ + map k A B f'.hom g.hom _ at hh
  simpa only [bottomMap, LinearMap.comp_apply, LinearMap.add_apply, map_add] using
    congrArg (cubicInsert k A B P Q t ⟨(t,0),Nat.add_zero t⟩) hh

theorem firstCubic_bottomMap (p : (n : ℕ) → P.X (n+3) ⟶ P.X n)
    (s n : ℕ) (f : U.X s ⟶ P.X (n+3)) (g : V.X 0 ⟶ Q.X 0) :
    (firstCubic k A B P Q p n).comp (bottomMap k A B P Q U V s (n+3) f g) =
      bottomMap k A B P Q U V s n (f ≫ p n) g := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, bottomMap, firstCubic_insert, firstCubicEntry]
  congr 1
  have hh := map_comp_apply k A B f (p n) g (𝟙 (Q.X 0))
    (bottomProjection k A B U V s x)
  simp only [Category.comp_id] at hh
  convert! hh using 1

theorem secondCubic_bottomMap (r : (n : ℕ) → Q.X (n+3) ⟶ Q.X n)
    (s n : ℕ) (f : U.X s ⟶ P.X (n+3)) (g : V.X 0 ⟶ Q.X 0) :
    (secondCubic k A B P Q r n).comp (bottomMap k A B P Q U V s (n+3) f g) = 0 := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, bottomMap, secondCubic_insert, secondCubicEntry,
    LinearMap.zero_apply]

end ArExplicit.ExternalTensor

end

end OAI

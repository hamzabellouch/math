import OAI.Algebra.Finitistic.Bimodule.BimoduleLeftTotalMap

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P P' P'' : BiComplex k B}
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ}

/-- Naturality of the actual bimodule-induced tensor map on arbitrary complexes. -/
theorem leftTotalMap_naturality (f : P ⟶ P') (g : Z ⟶ Z') :
    totalMap k B P p hp g ≫ leftTotalMap f Z' p hp =
      leftTotalMap f Z p hp ≫ totalMap k B P' p hp g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  change leftTermMap f Z' (p i) (n + -(p i))
    (((ComplexTensor.finiteTotalMap k B (right k B P) p hp g).f n).hom x i) =
      ((ComplexTensor.finiteTotalMap k B (right k B P') p hp g).f n).hom
        (leftTotalMapF f Z p n x) i
  erw [ComplexTensor.finiteTotalMap_apply,ComplexTensor.finiteTotalMap_apply]
  change leftTermMap f Z' (p i) (n + -(p i))
    (ComplexTensor.inputMap k B (right k B P) g (p i) (n + -(p i)) (x i)) =
      ComplexTensor.inputMap k B (right k B P') g (p i) (n + -(p i))
        (leftTermMap f Z (p i) (n + -(p i)) (x i))
  let L := (leftTermMap f Z' (p i) (n + -(p i))).toAddMonoidHom.comp
    (ComplexTensor.inputMap k B (right k B P) g (p i) (n + -(p i))).toAddMonoidHom
  let R := (ComplexTensor.inputMap k B (right k B P') g (p i) (n + -(p i))).toAddMonoidHom.comp
    (leftTermMap f Z (p i) (n + -(p i))).toAddMonoidHom
  induction x i using BalancedTensor.induction_on with
  | hz => exact L.map_zero.trans R.map_zero.symm
  | ht m n => rfl
  | ha x y hx hy =>
    exact (L.map_add x y).trans
      ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)

/-- An augmentation of bimodule complexes induces this concrete natural transformation. -/
def leftTensorNat (f : P ⟶ P') : functor k B P p hp ⟶ functor k B P' p hp where
  app Z := leftTotalMap f Z p hp
  naturality {_ _} g := leftTotalMap_naturality p hp f g

@[simp] theorem leftTotalMap_id (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    leftTotalMap (𝟙 P) Z p hp = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  change tensorAcross (𝟙 (P.X (p i))) (𝟙 (Z.X (n + -(p i)))) (x i) = x i
  rw [tensorAcross_id,LinearMap.id_apply]

@[simp] theorem leftTotalMap_comp (f : P ⟶ P') (g : P' ⟶ P'')
    (Z : CochainComplex (ModuleCat.{u} B) ℤ) :
    leftTotalMap (f ≫ g) Z p hp = leftTotalMap f Z p hp ≫ leftTotalMap g Z p hp := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  change tensorAcross ((f.f (p i)) ≫ g.f (p i)) (𝟙 (Z.X (n + -(p i)))) (x i) =
    tensorAcross (g.f (p i)) (𝟙 (Z.X (n + -(p i))))
      (tensorAcross (f.f (p i)) (𝟙 (Z.X (n + -(p i)))) (x i))
  have h := LinearMap.congr_fun (tensorAcross_comp (f.f (p i)) (g.f (p i))
    (𝟙 (Z.X (n + -(p i)))) (𝟙 (Z.X (n + -(p i))))) (x i)
  simpa only [Category.id_comp,LinearMap.comp_apply] using h.symm

/-- The finite signed total is functorial in the genuine bimodule complex too. -/
def leftTensorFunctor : BiComplex k B ⥤
    (CochainComplex (ModuleCat.{u} B) ℤ ⥤ CochainComplex (ModuleCat.{u} B) ℤ) where
  obj P := functor k B P p hp
  map f := leftTensorNat p hp f
  map_id P := by
    apply NatTrans.ext
    funext Z
    exact leftTotalMap_id p hp Z
  map_comp f g := by
    apply NatTrans.ext
    funext Z
    exact leftTotalMap_comp p hp f g Z
end LittleFinitistic.BimoduleTotal

end

end OAI

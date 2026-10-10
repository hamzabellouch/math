import OAI.Algebra.Finitistic.Rectification.InducedColumns
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.HomologicalComplexLimits

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

instance rightModuleK (N : ModuleCat.{u} Bᵐᵒᵖ) : Module k N :=
  Module.compHom N (algebraMap k Bᵐᵒᵖ)
instance rightModuleTower (N : ModuleCat.{u} Bᵐᵒᵖ) : IsScalarTower k Bᵐᵒᵖ N where
  smul_assoc r b n := by
    change (r • b) • n = (algebraMap k Bᵐᵒᵖ r) • (b • n)
    rw [Algebra.smul_def, mul_smul]
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule

abbrev Enveloping := B ⊗[k] Bᵐᵒᵖ
abbrev RightComplex := CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ
abbrev BiComplex := CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ

/-- Induction by the actual left ideal Be, on right modules and maps. -/
def columnFunctor (e : B) : ModuleCat.{u} Bᵐᵒᵖ ⥤ ModuleCat.{u} (Enveloping k B) where
  obj N := ModuleCat.of _ (Column k B N e)
  map f := ModuleCat.ofHom (columnMap k e f.hom)
  map_id N := by apply ModuleCat.hom_ext; exact map_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    simpa [columnMap] using (map_comp (k := k) (LinearMap.id) (LinearMap.id) f.hom g.hom)
instance columnFunctor_additive (e : B) : (columnFunctor k B e).Additive where
  map_add := by intros; apply ModuleCat.hom_ext; exact map_add_right _ _ _

instance columnFunctor_linear (e : B) : (columnFunctor k B e).Linear k where
  map_smul f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ExternalTensor.map (k := k) LinearMap.id (r • f.hom) x =
      (algebraMap k (Enveloping k B) r) • (columnMap k e f.hom x)
    rw [map_smul_right]
    exact (IsScalarTower.algebraMap_smul (Enveloping k B) r _).symm

abbrev columnComplex (e : B) : RightComplex B ⥤ BiComplex k B :=
  (columnFunctor k B e).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Right multiplication on the left tensor factor, natural in the right module. -/
def pathNat (ei ej a : B) (ha : a * ei = a) :
    columnFunctor k B ej ⟶ columnFunctor k B ei where
  app N := ModuleCat.ofHom (columnPath k ei ej a ha)
  naturality {N N'} f := by
    apply ModuleCat.hom_ext
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul c n => rfl
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

abbrev path (ei ej a : B) (ha : a * ei = a) (D : RightComplex B) :
    (columnComplex k B ej).obj D ⟶ (columnComplex k B ei).obj D :=
  ((pathNat k B ei ej a ha).mapHomologicalComplex (ComplexShape.up ℤ)).app D

@[reassoc] theorem path_naturality (ei ej a : B) (ha : a * ei = a)
    {D E : RightComplex B} (f : D ⟶ E) :
    (columnComplex k B ej).map f ≫ path k B ei ej a ha E =
      path k B ei ej a ha D ≫ (columnComplex k B ei).map f :=
  ((pathNat k B ei ej a ha).mapHomologicalComplex (ComplexShape.up ℤ)).naturality f

@[simp] theorem sum_f {C D : BiComplex k B} {I : Type} (s : Finset I)
    (f : I → (C ⟶ D)) (n : ℤ) : (∑ i ∈ s, f i).f n = ∑ i ∈ s, (f i).f n :=
  map_sum (Hom.fAddMonoidHom n) f s

@[simp] theorem sum_hom {S : Type*} [Ring S] {X Y : ModuleCat S}
    {I : Type} (s : Finset I) (f : I → (X ⟶ Y)) :
    (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  map_sum ModuleCat.homAddEquiv f s

private theorem sum_smul_component_apply {R : Type u} [Ring R] [Algebra k R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} {I J : Type} [Fintype I] [Fintype J]
    (r : I → J → k) (f : I → J → (K ⟶ L)) (n : ℤ) (x : K.X n) :
    ((∑ i, ∑ j, r i j • f i j).f n).hom x =
      ∑ i, ∑ j, algebraMap k R (r i j) • ((f i j).f n).hom x := by
  have eval_sum {I : Type} (s : Finset I) (g : I → (K ⟶ L)) :
      (∑ i ∈ s, g i).f n = ∑ i ∈ s, (g i).f n :=
    map_sum (Hom.fAddMonoidHom n) g s
  simp only [eval_sum, smul_f_apply, ModuleCat.hom_sum,
    ModuleCat.hom_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

/-- The vertex-zero component vanishes by the actual quadratic relation in B. -/
theorem paths_relation {A J : Type} [Fintype A] [Fintype J]
    (e₀ e₁ e₂ : B) (a : A → B) (b : J → B)
    (ha : ∀ i, a i * e₀ = a i) (hb : ∀ j, b j * e₁ = b j)
    (r : A → J → k) (hr : ∑ i, ∑ j, r i j • (b j * a i) = 0)
    (D : RightComplex B) :
    ∑ i, ∑ j, r i j • (path k B e₁ e₂ (b j) (hb j) D ≫
      path k B e₀ e₁ (a i) (ha i) D) = 0 := by
  apply Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  | tmul c v =>
    erw [sum_smul_component_apply]
    change (∑ i, ∑ j, (algebraMap k (Enveloping k B) (r i j)) •
      ((pathMap e₀ e₁ (a i) (ha i) (pathMap e₁ e₂ (b j) (hb j) c)) ⊗ₜ[k] v)) = 0
    simp only [IsScalarTower.algebraMap_smul, TensorProduct.smul_tmul',
      ← TensorProduct.sum_tmul]
    have hz : (∑ i, ∑ j, r i j •
        pathMap e₀ e₁ (a i) (ha i) (pathMap e₁ e₂ (b j) (hb j) c)) = 0 := by
      apply Subtype.ext
      change ((leftIdeal B e₀).subtype.restrictScalars k)
        (∑ i, ∑ j, r i j • pathMap e₀ e₁ (a i) (ha i)
          (pathMap e₁ e₂ (b j) (hb j) c)) = 0
      simp only [map_sum, map_smul, LinearMap.restrictScalars_apply,
        Submodule.subtype_apply, pathMap_apply]
      calc
        _ = (c : B) * (∑ i, ∑ j, r i j • (b j * a i)) := by
          simp only [Finset.mul_sum, Algebra.mul_smul_comm, mul_assoc]
        _ = 0 := by rw [hr, mul_zero]
    rw [hz, TensorProduct.zero_tmul]
end ExternalTensor.Section4

end

end OAI

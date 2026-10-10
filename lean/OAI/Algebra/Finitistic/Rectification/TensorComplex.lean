import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import OAI.Algebra.Finitistic.Rectification.TensorProjection
import OAI.Algebra.Finitistic.Encoding.RelationSequence

namespace OAI
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace LittleFinitistic.TensorComplex
attribute [local instance] ExternalTensor.rightModule
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

abbrev ScalarModule (N : ModuleCat.{u} Bᵐᵒᵖ) :=
  (ModuleCat.restrictScalars (algebraMap k Bᵐᵒᵖ)).obj N

instance scalarTower (N : ModuleCat.{u} Bᵐᵒᵖ) :
    IsScalarTower k Bᵐᵒᵖ (ScalarModule k B N) where
  smul_assoc c b n := by
    change (c • b) • (n : N) = algebraMap k Bᵐᵒᵖ c • (b • (n : N))
    rw [Algebra.smul_def,mul_smul]

variable {k B}
/-- The actual tensor differential, with the original right B-action. -/
def mapRight (M : ModuleCat.{u} k) {N N' : ModuleCat.{u} Bᵐᵒᵖ} (g : N ⟶ N') :
    (M ⊗[k] ScalarModule k B N) →ₗ[Bᵐᵒᵖ] (M ⊗[k] ScalarModule k B N') where
  __ := (TensorProduct.map LinearMap.id
    ((ModuleCat.restrictScalars (algebraMap k Bᵐᵒᵖ)).map g).hom).toAddMonoidHom
  map_smul' c x := by
    induction x using TensorProduct.inductionOn with
    | tmul m n =>
      change TensorProduct.mk k M (ScalarModule k B N') m (g.hom (c • (n : N))) = TensorProduct.mk k M (ScalarModule k B N') m (c • g.hom n)
      exact congrArg (TensorProduct.mk k M (ScalarModule k B N') m) (g.hom.map_smul c (n : N))
    | add x y hx hy => simp_all [smul_add]

@[simp] theorem mapRight_tmul (M : ModuleCat.{u} k) {N N' : ModuleCat.{u} Bᵐᵒᵖ}
    (g : N ⟶ N') (m : M) (n : ScalarModule k B N) :
    mapRight M g (m ⊗ₜ[k] n) = TensorProduct.mk k M (ScalarModule k B N') m (g.hom n) := rfl

variable (D : CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ)
/-- Tensor a vector space with every term and differential of the given right-module complex. -/
def complex (M : ModuleCat.{u} k) : CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ where
  X i := ModuleCat.of Bᵐᵒᵖ (M ⊗[k] ScalarModule k B (D.X i))
  d i j := ModuleCat.ofHom (mapRight M (D.d i j))
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m n =>
      have h : (D.d i j).hom (n : D.X i) = 0 := by rw [D.shape i j hij]; rfl
      exact (congrArg (TensorProduct.mk k M (ScalarModule k B (D.X j)) m) h).trans
        (map_zero (TensorProduct.mk k M (ScalarModule k B (D.X j)) m))
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  d_comp_d' i j l hij hjl := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m n =>
      change TensorProduct.mk k M (ScalarModule k B (D.X l)) m ((D.d j l).hom ((D.d i j).hom n)) = 0
      have h := congrArg (fun f : D.X i ⟶ D.X l => f.hom n) (D.d_comp_d i j l)
      change (D.d j l).hom ((D.d i j).hom n) = 0 at h
      exact (congrArg (TensorProduct.mk k M (ScalarModule k B (D.X l)) m) h).trans
        (map_zero (TensorProduct.mk k M (ScalarModule k B (D.X l)) m))
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- The first-factor tensor map is a chain map. -/
def complexMap {M M' : ModuleCat.{u} k} (f : M ⟶ M') : complex D M ⟶ complex D M' where
  f i := ModuleCat.ofHom (TensorProjection.rightMap (B := B)
    (N := ScalarModule k B (D.X i)) f.hom)
  comm' i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m n => rfl
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- The genuine additive tensor-with-D functor required by the path exact sequence. -/
def tensorFunctor : ModuleCat.{u} k ⥤ CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ where
  obj := complex D
  map := complexMap D
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m n => rfl
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m n => rfl
    | add x y hx hy =>
      exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

instance tensorFunctor_additive : (tensorFunctor (k := k) D).Additive where
  map_add {M M'} {f g} := by
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul m n => exact TensorProduct.add_tmul _ _ _
    | add x y hx hy =>
      change TensorProjection.rightMap (B := B) (f.hom + g.hom) (x+y) =
        TensorProjection.rightMap (B := B) f.hom (x+y) + TensorProjection.rightMap (B := B) g.hom (x+y)
      simp only [map_add]
      change TensorProjection.rightMap (B := B) (f.hom + g.hom) x =
        TensorProjection.rightMap (B := B) f.hom x + TensorProjection.rightMap (B := B) g.hom x at hx
      change TensorProjection.rightMap (B := B) (f.hom + g.hom) y =
        TensorProjection.rightMap (B := B) f.hom y + TensorProjection.rightMap (B := B) g.hom y at hy
      rw [hx,hy]
      abel

/-- The adjacent-vertex graded piece is the cone of the path-space identity. -/
theorem adjacent_total_acyclic (M : ModuleCat.{u} k) :
    (CochainComplex.mappingCone (𝟙 (complex D M))).Acyclic :=
  RectificationAcyclic.cone_acyclic _

/-- The source-0 path-relation graded piece is acyclic for the actual tensor functor. -/
theorem relation_total_acyclic {d t : ℕ} (P : QuadraticEncoding.Relations k d t) :
    (RectificationTotal.total ((RelationSequence.sequence P).map (tensorFunctor (k := k) D)).g
      ((RelationSequence.sequence P).map (tensorFunctor (k := k) D)).f
      (Homotopy.ofEq ((RelationSequence.sequence P).map (tensorFunctor (k := k) D)).zero)).Acyclic :=
  RelationSequence.realized_sequence_total_acyclic P (tensorFunctor (k := k) D)
end LittleFinitistic.TensorComplex

end

end OAI

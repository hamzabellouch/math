import OAI.Algebra.Finitistic.Rectification.ColumnProperties

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
noncomputable section
namespace ExternalTensor.Section4.ArrowVertex
attribute [local instance] ExternalTensor.bimodule ExternalTensor.rightModule
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]

/-- Left multiplication on a bimodule, regarded as a right-linear map. -/
def left (a : B) (N : ModuleCat.{u} (Enveloping k B)) :
    (forgetRight k B).obj N →ₗ[Bᵐᵒᵖ] (forgetRight k B).obj N where
  toFun x := (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (show N from x)
  map_add' x y := smul_add (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) (show N from x) (show N from y)
  map_smul' c x := by
    change (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • ((1 ⊗ₜ[k] c : Enveloping k B) • (show N from x)) =
      (1 ⊗ₜ[k] c : Enveloping k B) • ((a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (show N from x))
    erw [← mul_smul, ← mul_smul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

@[simp] theorem left_mul (a b : B) (N : ModuleCat.{u} (Enveloping k B))
    (x : (forgetRight k B).obj N) : left k B (a * b) N x = left k B a N (left k B b N x) := by
  change ((a * b) ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (show N from x) =
    (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • ((b ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (show N from x))
  erw [← mul_smul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

@[simp] theorem map_left {N N' : ModuleCat.{u} (Enveloping k B)}
    (f : N ⟶ N') (a : B) (x : (forgetRight k B).obj N) :
    (forgetRight k B).map f (left k B a N x) =
      left k B a N' ((forgetRight k B).map f x) := f.hom.map_smul _ _

/-- The actual fixed submodule eN, for an idempotent e. -/
def space (e : B) (N : ModuleCat.{u} (Enveloping k B)) :
    Submodule Bᵐᵒᵖ ((forgetRight k B).obj N) :=
  LinearMap.ker (left k B e N - LinearMap.id)

@[simp] theorem mem_space (e : B) (N : ModuleCat.{u} (Enveloping k B))
    (x : (forgetRight k B).obj N) : x ∈ space k B e N ↔ left k B e N x = x := by
  simp [space, LinearMap.mem_ker, sub_eq_zero]

/-- For idempotents the fixed submodule is exactly the image eN. -/
theorem space_eq_range (e : B) (he : e * e = e)
    (N : ModuleCat.{u} (Enveloping k B)) :
    space k B e N = (left k B e N).range := by
  ext x
  rw [mem_space, LinearMap.mem_range]
  constructor
  · intro hx
    exact ⟨x, hx⟩
  · rintro ⟨y, rfl⟩
    rw [← left_mul, he]

/-- Vertex restriction retains the original elements, rather than chosen coordinates. -/
def vertex (e : B) : ModuleCat.{u} (Enveloping k B) ⥤ ModuleCat.{u} Bᵐᵒᵖ where
  obj N := ModuleCat.of _ (space k B e N)
  map f := ModuleCat.ofHom
    { toFun x := ⟨(forgetRight k B).map f x.val, by
        rw [mem_space, ← map_left, (mem_space k B e _ _).1 x.property]⟩
      map_add' x y := Subtype.ext (map_add _ _ _)
      map_smul' c x := Subtype.ext (map_smul _ _ _) }
  map_id N := by ext x; rfl
  map_comp f g := by ext x; rfl
instance vertex_additive (e : B) : (vertex k B e).Additive where
  map_add := by intros; ext x; rfl

abbrev vertexComplex (e : B) : BiComplex k B ⥤ RightComplex B :=
  (vertex k B e).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The intervertex map is precisely left multiplication by a. -/
def arrow (ei ej a : B) (hja : ej * a = a) : vertex k B ei ⟶ vertex k B ej where
  app N := ModuleCat.ofHom
    { toFun x := ⟨left k B a N x.val, by
        rw [mem_space, ← left_mul, hja]⟩
      map_add' x y := Subtype.ext (map_add _ _ _)
      map_smul' c x := Subtype.ext (map_smul _ _ _) }
  naturality {N N'} f := by ext x; apply Subtype.ext; exact (map_left k B f a x.val).symm

abbrev arrowComplex (ei ej a : B) (hja : ej * a = a) (P : BiComplex k B) :
    (vertexComplex k B ei).obj P ⟶ (vertexComplex k B ej).obj P :=
  ((arrow k B ei ej a hja).mapHomologicalComplex (ComplexShape.up ℤ)).app P

@[simp] theorem arrow_original (ei ej a : B) (hja : ej * a = a)
    (P : BiComplex k B) (n : ℤ) (x : ((vertexComplex k B ei).obj P).X n) :
    (((arrowComplex k B ei ej a hja P).f n) x).val =
      (a ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • (show P.X n from x.val) := rfl

/-- Composition uses multiplication in B in the original arrow order. -/
@[reassoc] theorem arrow_comp (ei ej el a b : B) (hja : ej * a = a)
    (hlb : el * b = b) (hlba : el * (b * a) = b * a) (P : BiComplex k B) :
    arrowComplex k B ei ej a hja P ≫ arrowComplex k B ej el b hlb P =
      arrowComplex k B ei el (b * a) hlba P := by
  ext n x
  apply Subtype.ext
  exact (left_mul k B b a (P.X n) x.val).symm

/-- The trivial path acts as the identity on its vertex. -/
@[simp] theorem arrow_id (e : B) (he : e * e = e) (P : BiComplex k B) :
    arrowComplex k B e e e he P = 𝟙 ((vertexComplex k B e).obj P) := by
  ext n x
  apply Subtype.ext
  exact (mem_space k B e (P.X n) x.val).1 x.property

/-- The original diagonal tensor e tensor n in its actual fixed submodule. -/
def diagonal (e : B) (he : e * e = e) :
    𝟭 (ModuleCat.{u} Bᵐᵒᵖ) ⟶ columnFunctor k B e ⋙ vertex k B e where
  app N := ModuleCat.ofHom
    { toFun n := ⟨generator B e ⊗ₜ[k] n, by
        erw [mem_space]
        change (e • generator B e) ⊗ₜ[k] ((1 : Bᵐᵒᵖ) • n) = generator B e ⊗ₜ[k] n
        rw [one_smul]
        congr 1
        exact Subtype.ext he⟩
      map_add' x y := Subtype.ext (TensorProduct.tmul_add _ _ _)
      map_smul' c x := by
        apply Subtype.ext
        change generator B e ⊗ₜ[k] (c • x) =
          (1 ⊗ₜ[k] c : Enveloping k B) • (generator B e ⊗ₜ[k] x)
        rw [ExternalTensor.smul_tmul, one_smul] }
  naturality {N N'} f := by ext x; rfl

/-- Original insertion into a single induced column, degree by degree. -/
def diagonalComplex (e : B) (he : e * e = e) (D : RightComplex B) :
    D ⟶ (vertexComplex k B e).obj ((columnComplex k B e).obj D) where
  f n := (diagonal k B e he).app (D.X n)
  comm' i j _hij := (diagonal k B e he).naturality (D.d i j)

@[reassoc] theorem diagonal_naturality (e : B) (he : e * e = e)
    {D E : RightComplex B} (f : D ⟶ E) :
    f ≫ diagonalComplex k B e he E = diagonalComplex k B e he D ≫
      (vertexComplex k B e).map ((columnComplex k B e).map f) := by
  ext n x
  rfl

/-- Right multiplication in p at e_j agrees with left arrow action at e_i. -/
@[reassoc] theorem diagonal_path (ei ej a : B) (hei : ei * ei = ei)
    (hej : ej * ej = ej) (hai : a * ei = a) (hja : ej * a = a)
    (D : RightComplex B) :
    diagonalComplex k B ej hej D ≫ (vertexComplex k B ej).map (path k B ei ej a hai D) =
      diagonalComplex k B ei hei D ≫
        arrowComplex k B ei ej a hja ((columnComplex k B ei).obj D) := by
  ext n x
  apply Subtype.ext
  change (pathMap ei ej a hai (generator B ej)) ⊗ₜ[k] x =
    (a • generator B ei) ⊗ₜ[k] ((1 : Bᵐᵒᵖ) • x)
  rw [one_smul]
  congr 1
  apply Subtype.ext
  exact hja.trans hai.symm

@[reassoc] theorem arrow_naturality (ei ej a : B) (hja : ej * a = a)
    {P Q : BiComplex k B} (f : P ⟶ Q) :
    (vertexComplex k B ei).map f ≫ arrowComplex k B ei ej a hja Q =
      arrowComplex k B ei ej a hja P ≫ (vertexComplex k B ej).map f :=
  ((arrow k B ei ej a hja).mapHomologicalComplex (ComplexShape.up ℤ)).naturality f
end ExternalTensor.Section4.ArrowVertex

end

end OAI

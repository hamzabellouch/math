import OAI.Algebra.Finitistic.Rectification.ExternalTensor

namespace OAI
open scoped TensorProduct
noncomputable section

namespace ExternalTensor

attribute [local instance] bimodule rightModule

variable (k B : Type*) [Field k] [Ring B] [Algebra k B]

/-- The actual principal left ideal B e, the image of right multiplication by e. -/
def leftIdeal (e : B) : Submodule B B := (LinearMap.mulRight B e).range

@[simp] theorem mem_leftIdeal (e x : B) : x ∈ leftIdeal B e ↔ ∃ b : B, b * e = x :=
  Iff.rfl

theorem leftIdeal_finiteDimensional [FiniteDimensional k B] (e : B) :
    FiniteDimensional k (leftIdeal B e) :=
  FiniteDimensional.of_injective ((leftIdeal B e).subtype.restrictScalars k)
    Subtype.val_injective

attribute [local instance] leftIdeal_finiteDimensional

variable (N : Type*) [AddCommGroup N] [Module k N]
  [Module Bᵐᵒᵖ N] [IsScalarTower k Bᵐᵒᵖ N]

/-- The induced column in Section 4, with its external actions. -/
abbrev Column (e : B) := (leftIdeal B e) ⊗[k] N

theorem column_projective (e : B) [Module.Projective Bᵐᵒᵖ N] :
    Module.Projective Bᵐᵒᵖ (Column k B N e) :=
  projective_right k B (leftIdeal B e) N

theorem column_finite_right [FiniteDimensional k B] (e : B)
    [Module.Finite Bᵐᵒᵖ N] : Module.Finite Bᵐᵒᵖ (Column k B N e) :=
  finite_right k B (leftIdeal B e) N

theorem column_finiteDimensional [FiniteDimensional k B] (e : B)
    [Module.Finite Bᵐᵒᵖ N] : FiniteDimensional k (Column k B N e) := by
  let : Module.Finite k N := Module.Finite.trans Bᵐᵒᵖ N
  exact finiteDimensional k (leftIdeal B e) N

/-- The full induced-column assertion required for each summand of L'_0,L'_1,L'_2. -/
theorem induced_column [FiniteDimensional k B] (e : B)
    [Module.Finite Bᵐᵒᵖ N] [Module.Projective Bᵐᵒᵖ N] :
    FiniteDimensional k (Column k B N e) ∧
      Module.Finite Bᵐᵒᵖ (Column k B N e) ∧
      Module.Projective Bᵐᵒᵖ (Column k B N e) :=
  ⟨column_finiteDimensional k B N e, column_finite_right k B N e,
    column_projective k B N e⟩


/-- The distinguished generator e of the principal left ideal. -/
def generator (e : B) : leftIdeal B e := ⟨e, ⟨1, one_mul e⟩⟩

/-- The right-linear insertion used in the vertex maps iota_i. -/
def columnInclusion (e : B) : N →ₗ[Bᵐᵒᵖ] Column k B N e where
  toFun n := generator B e ⊗ₜ[k] n
  map_add' first second := TensorProduct.tmul_add _ first second
  map_smul' c n := (right_smul_tmul k B (leftIdeal B e) N c (generator B e) n).symm

@[simp] theorem columnInclusion_apply (e : B) (n : N) :
    columnInclusion k B N e n = generator B e ⊗ₜ[k] n := rfl

variable {B}
/-- Right multiplication by a path a: i→j maps B e_j to B e_i.
Only the relation a e_i = a is needed for membership in the target ideal. -/
def pathMap (ei ej a : B) (ha : a * ei = a) :
    leftIdeal B ej →ₗ[B] leftIdeal B ei where
  toFun c := ⟨c.val * a, ⟨c.val * a, by simp [LinearMap.mulRight_apply, mul_assoc, ha]⟩⟩
  map_add' c d := Subtype.ext (add_mul c.val d.val a)
  map_smul' b c := Subtype.ext (mul_assoc b c.val a)

@[simp] theorem pathMap_apply (ei ej a : B) (ha : a * ei = a) (c : leftIdeal B ej) :
    (pathMap ei ej a ha c : B) = (c : B) * a := rfl

variable {N}
/-- The path-multiplication component c tensor n ↦ ca tensor n of the rectification maps. -/
def columnPath (ei ej a : B) (ha : a * ei = a) :
    Column k B N ej →ₗ[B ⊗[k] Bᵐᵒᵖ] Column k B N ei :=
  map (k := k) (pathMap ei ej a ha) LinearMap.id

@[simp] theorem columnPath_tmul (ei ej a : B) (ha : a * ei = a)
    (c : leftIdeal B ej) (n : N) :
    columnPath k ei ej a ha (c ⊗ₜ[k] n) = (pathMap ei ej a ha c) ⊗ₜ[k] n := rfl

variable {N' : Type*} [AddCommGroup N'] [Module k N']
  [Module Bᵐᵒᵖ N'] [IsScalarTower k Bᵐᵒᵖ N']

/-- The differential or relation-homotopy component c tensor n ↦ c tensor f(n). -/
def columnMap (e : B) (f : N →ₗ[Bᵐᵒᵖ] N') :
    Column k B N e →ₗ[B ⊗[k] Bᵐᵒᵖ] Column k B N' e :=
  map (k := k) LinearMap.id f

@[simp] theorem columnMap_tmul (e : B) (f : N →ₗ[Bᵐᵒᵖ] N')
    (c : leftIdeal B e) (n : N) :
    columnMap k e f (c ⊗ₜ[k] n) = c ⊗ₜ[k] f n := rfl
end ExternalTensor

end

end OAI

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Tactic.Ring

namespace OAI

namespace ArExplicit

inductive Letter
  | e | x | y | z | u | v | t | j | f | n
  deriving DecidableEq

instance : Fintype Letter where
  elems := {.e, .x, .y, .z, .u, .v, .t, .j, .f, .n}
  complete i := by cases i <;> simp

@[simp] theorem Letter.card : Fintype.card Letter = 10 := by decide

@[ext]
structure BaseAlgebra (k : Type*) (q : k) where
  coeff : Letter → k

namespace BaseAlgebra

variable {k : Type*} (q : k)

def coordinates : BaseAlgebra k q ≃ (Letter → k) where
  toFun := coeff
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance [AddCommGroup k] : AddCommGroup (BaseAlgebra k q) :=
  (coordinates q).addCommGroup

variable [CommRing k]

def coordinateAddEquiv : BaseAlgebra k q ≃+ (Letter → k) where
  __ := coordinates q
  map_add' _ _ := rfl

instance : Module k (BaseAlgebra k q) := (coordinateAddEquiv q).module k

@[simp] theorem coeff_zero (i : Letter) : (0 : BaseAlgebra k q).coeff i = 0 := rfl
@[simp] theorem coeff_add (a b : BaseAlgebra k q) (i : Letter) :
    (a + b).coeff i = a.coeff i + b.coeff i := rfl
@[simp] theorem coeff_neg (a : BaseAlgebra k q) (i : Letter) :
    (-a).coeff i = -a.coeff i := rfl
@[simp] theorem coeff_smul (r : k) (a : BaseAlgebra k q) (i : Letter) :
    (r • a).coeff i = r * a.coeff i := rfl

open Letter

def product (a b : BaseAlgebra k q) : BaseAlgebra k q := ⟨fun
  | e => a.coeff e * b.coeff e
  | x => a.coeff e * b.coeff x + a.coeff x * b.coeff e + q * a.coeff u * b.coeff t
  | y => a.coeff e * b.coeff y + a.coeff y * b.coeff e + a.coeff u * b.coeff t
  | z => a.coeff e * b.coeff z + a.coeff z * b.coeff e + q * a.coeff x * b.coeff y +
      a.coeff y * b.coeff x + q * a.coeff v * b.coeff t + a.coeff u * b.coeff j
  | u => a.coeff e * b.coeff u + a.coeff u * b.coeff f
  | v => a.coeff e * b.coeff v + a.coeff v * b.coeff f + a.coeff x * b.coeff u +
      a.coeff y * b.coeff u + a.coeff u * b.coeff n
  | t => a.coeff f * b.coeff t + a.coeff t * b.coeff e
  | j => a.coeff f * b.coeff j + a.coeff j * b.coeff e + a.coeff t * b.coeff x +
      q ^ 2 * a.coeff t * b.coeff y + q * a.coeff n * b.coeff t
  | f => a.coeff f * b.coeff f
  | n => a.coeff f * b.coeff n + a.coeff n * b.coeff f +
      (1 + q) * a.coeff t * b.coeff u⟩

instance : Mul (BaseAlgebra k q) := ⟨product q⟩
instance : One (BaseAlgebra k q) := ⟨⟨fun i => if i = e ∨ i = f then 1 else 0⟩⟩

@[simp] theorem coeff_mul (a b : BaseAlgebra k q) :
    (a * b).coeff = (product q a b).coeff := rfl
@[simp] theorem coeff_one (i : Letter) :
    (1 : BaseAlgebra k q).coeff i = if i = e ∨ i = f then 1 else 0 := rfl

private theorem product_assoc (a b c : BaseAlgebra k q) : (a * b) * c = a * (b * c) := by
  ext i
  cases i <;> simp only [coeff_mul, product] <;> ring

instance : Ring (BaseAlgebra k q) where
  __ := (inferInstance : AddCommGroup (BaseAlgebra k q))
  mul_assoc := product_assoc q
  one_mul a := by ext i; cases i <;> simp [product]
  mul_one a := by ext i; cases i <;> simp [product]
  left_distrib a b c := by
    ext i
    cases i <;> simp only [coeff_mul, product, coeff_add] <;> ring
  right_distrib a b c := by
    ext i
    cases i <;> simp only [coeff_mul, product, coeff_add] <;> ring
  zero_mul a := by ext i; cases i <;> simp [product]
  mul_zero a := by ext i; cases i <;> simp [product]

instance : Algebra k (BaseAlgebra k q) :=
  Algebra.ofModule
    (by intro r a b; ext i; cases i <;> simp only [coeff_smul, coeff_mul, product] <;> ring)
    (by intro r a b; ext i; cases i <;> simp only [coeff_smul, coeff_mul, product] <;> ring)

def basisVector (i : Letter) : BaseAlgebra k q := ⟨Pi.single i 1⟩

@[simp] theorem coeff_basisVector (i l : Letter) :
    (basisVector q i).coeff l = if l = i then 1 else 0 := by
  simp [basisVector, Pi.single_apply, eq_comm]

theorem one_eq_vertices : (1 : BaseAlgebra k q) = basisVector q e + basisVector q f := by
  ext i
  cases i <;> simp

def multiplicationTable (left right : Letter) : BaseAlgebra k q :=
  let b := basisVector q
  match left, right with
  | e, e => b e
  | e, x => b x
  | e, y => b y
  | e, z => b z
  | e, u => b u
  | e, v => b v
  | x, e => b x
  | x, y => q • b z
  | x, u => b v
  | y, e => b y
  | y, x => b z
  | y, u => b v
  | z, e => b z
  | u, f => b u
  | u, t => b y + q • b x
  | u, j => b z
  | u, n => b v
  | v, f => b v
  | v, t => q • b z
  | t, e => b t
  | t, x => b j
  | t, y => q ^ 2 • b j
  | t, u => (1 + q) • b n
  | j, e => b j
  | f, t => b t
  | f, j => b j
  | f, f => b f
  | f, n => b n
  | n, f => b n
  | n, t => q • b j
  | _, _ => 0

private theorem basis_e_mul (right : Letter) :
    basisVector q e * basisVector q right = multiplicationTable q e right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

private theorem basis_x_mul (right : Letter) :
    basisVector q x * basisVector q right = multiplicationTable q x right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

private theorem basis_y_mul (right : Letter) :
    basisVector q y * basisVector q right = multiplicationTable q y right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

private theorem basis_z_mul (right : Letter) :
    basisVector q z * basisVector q right = multiplicationTable q z right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

private theorem basis_u_mul (right : Letter) :
    basisVector q u * basisVector q right = multiplicationTable q u right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

private theorem basis_v_mul (right : Letter) :
    basisVector q v * basisVector q right = multiplicationTable q v right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

private theorem basis_t_mul (right : Letter) :
    basisVector q t * basisVector q right = multiplicationTable q t right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

private theorem basis_j_mul (right : Letter) :
    basisVector q j * basisVector q right = multiplicationTable q j right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

private theorem basis_f_mul (right : Letter) :
    basisVector q f * basisVector q right = multiplicationTable q f right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

private theorem basis_n_mul (right : Letter) :
    basisVector q n * basisVector q right = multiplicationTable q n right := by
  cases right <;> ext coordinate <;> cases coordinate <;>
    simp [product, multiplicationTable]

theorem basis_mul (left right : Letter) :
    basisVector q left * basisVector q right = multiplicationTable q left right := by
  cases left
  · exact basis_e_mul q right
  · exact basis_x_mul q right
  · exact basis_y_mul q right
  · exact basis_z_mul q right
  · exact basis_u_mul q right
  · exact basis_v_mul q right
  · exact basis_t_mul q right
  · exact basis_j_mul q right
  · exact basis_f_mul q right
  · exact basis_n_mul q right

theorem fourfold_product :
    ((basisVector q u * basisVector q t) * basisVector q u) * basisVector q t =
      (q * (1 + q)) • basisVector q z := by
  ext coordinate
  cases coordinate <;> simp [product]
  ring

def mapScalars {K : Type*} [CommRing K] (f : k →+* K) :
    BaseAlgebra k q →+* BaseAlgebra K (f q) where
  toFun a := ⟨fun i => f (a.coeff i)⟩
  map_one' := by ext i; cases i <;> simp
  map_mul' a b := by
    ext i
    cases i <;> simp [product, map_add, map_mul, map_pow]
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

@[simp] theorem coeff_mapScalars {K : Type*} [CommRing K] (f : k →+* K)
    (a : BaseAlgebra k q) (i : Letter) :
    (mapScalars q f a).coeff i = f (a.coeff i) := rfl

theorem mapScalars_injective {K : Type*} [CommRing K] (f : k →+* K)
    (hf : Function.Injective f) : Function.Injective (mapScalars q f) := by
  intro a b h
  ext i
  apply hf
  exact congrArg (fun c : BaseAlgebra K (f q) => c.coeff i) h

def coordinateLinearEquiv : BaseAlgebra k q ≃ₗ[k] (Letter → k) :=
  (coordinateAddEquiv q).linearEquiv k

instance : Module.Finite k (BaseAlgebra k q) :=
  Module.Finite.equiv (coordinateLinearEquiv q).symm

theorem finrank_eq_ten [Nontrivial k] : Module.finrank k (BaseAlgebra k q) = 10 := by
  rw [(coordinateLinearEquiv q).finrank_eq]
  simp only [Module.finrank_fintype_fun_eq_card, Letter.card]

theorem fourfold_product_ne_zero [IsDomain k] (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    ((basisVector q u * basisVector q t) * basisVector q u) * basisVector q t ≠ 0 := by
  rw [fourfold_product]
  intro h
  have hz := congrArg (fun a : BaseAlgebra k q => a.coeff z) h
  simpa using (mul_ne_zero hq hq1) (by simpa using hz)

end BaseAlgebra
end ArExplicit

end OAI

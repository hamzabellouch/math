import Mathlib

namespace OAI


/-!
Nonunital correction, Steinberg groups, corners, and kernel annihilation.
-/


namespace FiniteAlgebraicEnvelopes

universe u


/-! The correction for a nonunital coefficient map in the affine transition and product identities.
The proof works over a noncommutative ring. -/


section NonunitalCorrection
variable {R S : Type*} [Ring R] [Ring S]

/-- Adjoining the unchanged complementary identity to a nonunital map. -/
def correctedMap (ψ : R →ₙ+* S) : R →* S where
  toFun x := 1 + ψ (x - 1)
  map_one' := by simp
  map_mul' x y := by
    have h : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by
      noncomm_ring
    rw [h, map_add, map_add, map_mul]
    noncomm_ring

@[simp] theorem correctedMap_apply (ψ : R →ₙ+* S) (x : R) :
    correctedMap ψ x = 1 + ψ (x - 1) := rfl

theorem correctedMap_injective (ψ : R →ₙ+* S) (hψ : Function.Injective ψ) :
    Function.Injective (correctedMap ψ) := by
  intro x y h
  have hsub : x - 1 = y - 1 := hψ (add_left_cancel h)
  exact sub_left_inj.mp hsub

/-- Entrywise extension before adjoining the unchanged identity. -/
def matrixNonunitalMap {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : R →ₙ+* S) :
    Matrix ι ι R →ₙ+* Matrix ι ι S where
  toFun A := A.map ψ
  map_zero' := by ext; simp
  map_add' A B := by ext; simp
  map_mul' A B := Matrix.map_mul

@[simp] theorem matrixNonunitalMap_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : R →ₙ+* S) (A : Matrix ι ι R) : matrixNonunitalMap ψ A = A.map ψ := rfl

end NonunitalCorrection


/-! The Steinberg presentation in the Steinberg kernel argument.  No stability or centrality
 theorem is assumed.  Root indices are restricted to the off-diagonal. -/
namespace Steinberg
open scoped commutatorElement

abbrev Index (ι : Type*) := {p : ι × ι // p.1 ≠ p.2}
abbrev Generator (ι R : Type*) := Index ι × R

def freeRoot {ι R : Type*} (i j : ι) (h : i ≠ j) (a : R) :
    FreeGroup (Generator ι R) := FreeGroup.of (⟨(i, j), h⟩, a)

inductive Relation (ι R : Type*) [Ring R] : FreeGroup (Generator ι R) → Prop
  | additive (i j : ι) (h : i ≠ j) (a b : R) :
      Relation ι R (freeRoot i j h a * freeRoot i j h b *
        (freeRoot i j h (a + b))⁻¹)
  | chain (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
      Relation ι R (⁅freeRoot i j hij a, freeRoot j k hjk b⁆ *
        (freeRoot i k hik (a * b))⁻¹)
  | distant (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
      (hil : i ≠ l) (hjk : j ≠ k) (a b : R) :
      Relation ι R ⁅freeRoot i j hij a, freeRoot k l hkl b⁆

abbrev Group (ι R : Type*) [Ring R] := PresentedGroup {w | Relation ι R w}

variable {ι R S : Type*} [Ring R] [Ring S]

def root (i j : ι) (h : i ≠ j) (a : R) : Group ι R :=
  PresentedGroup.of (⟨(i, j), h⟩, a)

@[simp] theorem mk_freeRoot (i j : ι) (h : i ≠ j) (a : R) :
    PresentedGroup.mk {w | Relation ι R w} (freeRoot i j h a) = root i j h a := rfl

theorem root_add (i j : ι) (h : i ≠ j) (a b : R) :
    root i j h a * root i j h b = root i j h (a + b) := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Relation.additive i j h a b)

theorem root_chain (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) : ⁅root i j hij a, root j k hjk b⁆ = root i k hik (a * b) := by
  simpa only [map_commutatorElement, mk_freeRoot] using
    (PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := {w | Relation ι R w}) (Relation.chain i j k hij hjk hik a b))

theorem root_distant (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
    (hil : i ≠ l) (hjk : j ≠ k) (a b : R) :
    Commute (root i j hij a) (root k l hkl b) := by
  apply commutatorElement_eq_one_iff_commute.mp
  simpa only [map_commutatorElement, mk_freeRoot] using
    PresentedGroup.one_of_mem (rels := {w | Relation ι R w}) (Relation.distant i j k l hij hkl hil hjk a b)

@[simp] theorem root_zero (i j : ι) (h : i ≠ j) : root i j h (0 : R) = 1 := by
  have h0 := root_add i j h (0 : R) 0
  simpa using h0

@[simp] theorem root_neg (i j : ι) (h : i ≠ j) (a : R) :
    root i j h (-a) = (root i j h a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [root_add, add_neg_cancel, root_zero]

/-- Every additive multiplicative coefficient map induces a Steinberg map;
it is not required to preserve one. -/
def coefficientMap (ψ : R →ₙ+* S) : Group ι R →* Group ι S :=
  PresentedGroup.toGroup (f := fun z : Generator ι R =>
    root z.1.1.1 z.1.1.2 z.1.2 (ψ z.2)) (by
      intro w hw
      cases hw with
      | additive i j h a b =>
        simp only [map_mul, map_inv, freeRoot, FreeGroup.lift_apply_of, map_add]
        rw [root_add, mul_inv_cancel]
      | chain i j k hij hjk hik a b =>
        simp only [map_mul, map_inv, map_commutatorElement, freeRoot,
          FreeGroup.lift_apply_of, map_mul]
        rw [root_chain i j k hij hjk hik, mul_inv_cancel]
      | distant i j k l hij hkl hil hjk a b =>
        simp only [map_commutatorElement, freeRoot, FreeGroup.lift_apply_of]
        exact (root_distant i j k l hij hkl hil hjk (ψ a) (ψ b)).commutator_eq)

@[simp] theorem coefficientMap_root (ψ : R →ₙ+* S) (i j : ι) (h : i ≠ j) (a : R) :
    coefficientMap ψ (root i j h a) = root i j h (ψ a) :=
  PresentedGroup.toGroup.of _


section TotalRoots
variable [DecidableEq ι]

/-- A total notation: the unused diagonal root is the identity. -/
def x (i j : ι) (a : R) : Group ι R := if h : i = j then 1 else root i j h a

@[simp] theorem x_self (i : ι) (a : R) : x i i a = 1 := by simp [x]

theorem x_of_ne (i j : ι) (h : i ≠ j) (a : R) : x i j a = root i j h a := by
  simp [x, h]

@[simp] theorem x_zero (i j : ι) : x i j (0 : R) = 1 := by
  unfold x
  split_ifs <;> simp

theorem x_add (i j : ι) (a b : R) : x i j (a + b) = x i j a * x i j b := by
  by_cases h : i = j
  · subst j; simp
  · simp only [x_of_ne i j h]
    exact (root_add i j h a b).symm

@[simp] theorem x_neg (i j : ι) (a : R) : x i j (-a) = (x i j a)⁻¹ := by
  by_cases h : i = j
  · subst j; simp
  · simp only [x_of_ne i j h, root_neg]

theorem x_distant (i j k l : ι) (hil : i ≠ l) (hjk : j ≠ k) (a b : R) :
    Commute (x i j a) (x k l b) := by
  by_cases hij : i = j
  · subst j; simp
  by_cases hkl : k = l
  · subst l; simp
  simp only [x_of_ne i j hij, x_of_ne k l hkl]
  exact root_distant i j k l hij hkl hil hjk a b

theorem x_chain (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) : ⁅x i j a, x j k b⁆ = x i k (a * b) := by
  simp only [x_of_ne i j hij, x_of_ne j k hjk, x_of_ne i k hik]
  exact root_chain i j k hij hjk hik a b

/-- Additive root parametrization, without assuming a commutative ring. -/
def xAddHom (i j : ι) : R →+ Additive (Group ι R) where
  toFun a := Additive.ofMul (x i j a)
  map_zero' := x_zero i j
  map_add' := x_add i j

@[simp] theorem xAddHom_apply (i j : ι) (a : R) :
    xAddHom i j a = Additive.ofMul (x i j a) := rfl

end TotalRoots

section MatrixRepresentation
variable [Fintype ι] [DecidableEq ι]

/-- Elementary matrices over an arbitrary, possibly noncommutative, ring. -/
def elementary (i j : ι) (h : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := 1 + Matrix.single i j a
  inv := 1 - Matrix.single i j a
  val_inv := by
    have h0 : Matrix.single i j a * Matrix.single i j a = 0 :=
      Matrix.single_mul_single_of_ne a i j i h.symm a
    calc
      (1 + Matrix.single i j a) * (1 - Matrix.single i j a) =
          1 - Matrix.single i j a * Matrix.single i j a := by noncomm_ring
      _ = 1 := by rw [h0, sub_zero]
  inv_val := by
    have h0 : Matrix.single i j a * Matrix.single i j a = 0 :=
      Matrix.single_mul_single_of_ne a i j i h.symm a
    calc
      (1 - Matrix.single i j a) * (1 + Matrix.single i j a) =
          1 - Matrix.single i j a * Matrix.single i j a := by noncomm_ring
      _ = 1 := by rw [h0, sub_zero]

@[simp] theorem elementary_val (i j : ι) (h : i ≠ j) (a : R) :
    (elementary i j h a : Matrix ι ι R) = 1 + Matrix.single i j a := rfl

@[simp] theorem elementary_inv_val (i j : ι) (h : i ≠ j) (a : R) :
    ((elementary i j h a)⁻¹).val = 1 - Matrix.single i j a := rfl

theorem elementary_add (i j : ι) (h : i ≠ j) (a b : R) :
    elementary i j h a * elementary i j h b = elementary i j h (a + b) := by
  apply Units.ext
  simp only [Units.val_mul, elementary_val, Matrix.single_add]
  simp only [add_mul, mul_add, one_mul, mul_one,
    Matrix.single_mul_single_of_ne a i j i h.symm b, add_zero]
  abel

theorem elementary_chain (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) : ⁅elementary i j hij a, elementary j k hjk b⁆ =
      elementary i k hik (a * b) := by
  apply Units.ext
  simp only [commutatorElement_def, Units.val_mul, elementary_val, elementary_inv_val]
  simp only [add_mul, mul_add, mul_sub, sub_mul, one_mul, mul_one,
    Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ hij.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hik.symm, zero_mul]
  noncomm_ring

theorem elementary_distant (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l)
    (hil : i ≠ l) (hjk : j ≠ k) (a b : R) :
    Commute (elementary i j hij a) (elementary k l hkl b) := by
  apply Units.ext
  simp only [Units.val_mul, elementary_val, add_mul, mul_add, one_mul, mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk,
    Matrix.single_mul_single_of_ne _ _ _ _ hil.symm, add_zero]
  abel

/-- The matrix action of the presented Steinberg group.  Its codomain here is
all matrix units rather than the equal image subgroup E_n(R). -/
def matrixMap : Group ι R →* (Matrix ι ι R)ˣ :=
  PresentedGroup.toGroup (f := fun z : Generator ι R =>
    elementary z.1.1.1 z.1.1.2 z.1.2 z.2) (by
      intro w hw
      cases hw with
      | additive i j h a b =>
        simp only [map_mul, map_inv, freeRoot, FreeGroup.lift_apply_of]
        rw [elementary_add, mul_inv_cancel]
      | chain i j k hij hjk hik a b =>
        simp only [map_mul, map_inv, map_commutatorElement, freeRoot,
          FreeGroup.lift_apply_of]
        rw [elementary_chain i j k hij hjk hik, mul_inv_cancel]
      | distant i j k l hij hkl hil hjk a b =>
        simp only [map_commutatorElement, freeRoot, FreeGroup.lift_apply_of]
        exact (elementary_distant i j k l hij hkl hil hjk a b).commutator_eq)

@[simp] theorem matrixMap_root (i j : ι) (h : i ≠ j) (a : R) :
    matrixMap (root i j h a) = elementary i j h a := PresentedGroup.toGroup.of _

/-- Naturality of the matrix action for a nonunital coefficient map. -/
theorem matrixMap_coefficientMap (ψ : R →ₙ+* S) (z : Group ι R) :
    matrixMap (coefficientMap ψ z) =
      Units.map (correctedMap (matrixNonunitalMap ψ)) (matrixMap z) := by
  have h : (matrixMap (ι := ι) (R := S)).comp (coefficientMap ψ) =
      (Units.map (correctedMap (matrixNonunitalMap ψ))).comp matrixMap := by
    apply PresentedGroup.ext
    rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
    change matrixMap (coefficientMap ψ (root i j hij a)) =
      Units.map _ (matrixMap (root i j hij a))
    rw [coefficientMap_root, matrixMap_root, matrixMap_root]
    apply Units.ext
    change 1 + Matrix.single i j (ψ a) =
      1 + ((1 + Matrix.single i j a) - 1).map ψ
    rw [add_sub_cancel_left, Matrix.map_single _ _ _ ψ]
  exact DFunLike.congr_fun h z

/-- In particular, coefficient maps preserve the full matrix kernel. -/
theorem coefficientMap_preserves_kernel (ψ : R →ₙ+* S) (z : Group ι R)
    (hz : matrixMap z = 1) : matrixMap (coefficientMap ψ z) = 1 := by
  rw [matrixMap_coefficientMap, hz, map_one]

/- The row-and-column argument of the Steinberg kernel argument starts with the column roots.
Taking a finite coproduct is legitimate because these root subgroups commute. -/

omit [Fintype ι] in
theorem column_roots_commute (i j k : ι) (a b : R) :
    Commute (x i k a) (x j k b) := by
  by_cases hi : i = k
  · subst i; simp
  by_cases hj : j = k
  · subst j; simp
  exact x_distant i k j k hi (Ne.symm hj) a b

def columnAddHom (k : ι) : (ι → R) →+ Additive (Group ι R) :=
  AddMonoidHom.noncommPiCoprod (fun i => xAddHom i k) (by
    intro i j _ a b
    exact column_roots_commute i j k a b)

def column (k : ι) (v : ι → R) : Group ι R := (columnAddHom k v).toMul

@[simp] theorem column_single (k i : ι) (a : R) :
    column k (Pi.single i a) = x i k a :=
  congrArg Additive.toMul (AddMonoidHom.noncommPiCoprod_single (fun i => xAddHom i k) i a)

@[simp] theorem column_zero (k : ι) : column k (0 : ι → R) = 1 :=
  (columnAddHom k).map_zero

theorem column_add (k : ι) (v w : ι → R) :
    column k (v + w) = column k v * column k w := (columnAddHom k).map_add v w

/-- Left multiplication of columns, viewed purely additively. -/
def mulVecAddHom (A : Matrix ι ι R) : (ι → R) →+ (ι → R) where
  toFun v := Matrix.mulVec A v
  map_zero' := Matrix.mulVec_zero A
  map_add' := Matrix.mulVec_add A

omit [DecidableEq ι] in
@[simp] theorem mulVecAddHom_apply (A : Matrix ι ι R) (v : ι → R) :
    mulVecAddHom A v = Matrix.mulVec A v := rfl

/-- Additive notation for conjugation in the Steinberg group. -/
def conjugateAddHom (g : Group ι R) : Additive (Group ι R) →+ Additive (Group ι R) :=
  (MulAut.conj g).toMonoidHom.toAdditive

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem conjugateAddHom_apply (g z : Group ι R) :
    conjugateAddHom g (Additive.ofMul z) = Additive.ofMul (g * z * g⁻¹) := rfl

theorem elementary_mulVec (i j : ι) (h : i ≠ j) (a : R) (v : ι → R) :
    Matrix.mulVec (elementary i j h a).val v = v + Pi.single i (a * v j) := by
  rw [elementary_val, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

/-- Conjugation by one root acts on the external column as its elementary matrix. -/
theorem x_conjugate_column (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : R) (v : ι → R) :
    x i j a * column k v * (x i j a)⁻¹ =
      column k (Matrix.mulVec (elementary i j hij a).val v) := by
  have hh : (conjugateAddHom (x i j a)).comp (columnAddHom k) =
      (columnAddHom k).comp (mulVecAddHom (elementary i j hij a).val) := by
    apply AddMonoidHom.pi_ext
    intro l b
    change x i j a * column k (Pi.single l b) * (x i j a)⁻¹ =
      column k (Matrix.mulVec (elementary i j hij a).val (Pi.single l b))
    rw [column_single, elementary_mulVec, column_add, column_single, column_single]
    by_cases hlj : l = j
    · subst l
      rw [Pi.single_eq_same]
      calc
        x i j a * x j k b * (x i j a)⁻¹ = ⁅x i j a, x j k b⁆ * x j k b := by
          simp [commutatorElement_def, mul_assoc]
        _ = x i k (a * b) * x j k b := by rw [x_chain i j k hij hjk hik]
        _ = x j k b * x i k (a * b) := (column_roots_commute i j k (a * b) b).eq
    · rw [Pi.single_eq_of_ne (Ne.symm hlj), mul_zero, x_zero, mul_one]
      rw [(x_distant i j l k hik (Ne.symm hlj) a b).eq, mul_inv_cancel_right]
  exact DFunLike.congr_fun hh v

/-- Words generated without using the index k. -/
def omitting (k : ι) : Subgroup (Group ι R) :=
  Subgroup.closure {g | ∃ (i j : ι) (a : R), i ≠ k ∧ j ≠ k ∧ g = x i j a}

omit [Fintype ι] in
 theorem x_mem_omitting (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) (a : R) :
    x i j a ∈ omitting k := Subgroup.subset_closure ⟨i, j, a, hik, hjk, rfl⟩

/-- External-column action for an arbitrary word omitting k, not just for generators. -/
theorem conjugate_column_of_mem_omitting (k : ι) {z : Group ι R} (hz : z ∈ omitting k)
    (v : ι → R) : z * column k v * z⁻¹ = column k (Matrix.mulVec (matrixMap z).val v) := by
  induction hz using Subgroup.closure_induction generalizing v with
  | mem z hz =>
    obtain ⟨i, j, a, hik, hjk, rfl⟩ := hz
    by_cases hij : i = j
    · subst j; simp
    rw [x_of_ne i j hij, matrixMap_root, ← x_of_ne i j hij]
    exact x_conjugate_column i j k hij hik hjk a v
  | one => simp
  | mul z w _ _ ihz ihw =>
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← ihz, ← ihw]
    group
  | inv z _ ih =>
    have h := ih (Matrix.mulVec ((matrixMap z)⁻¹).val v)
    have hv : Matrix.mulVec (matrixMap z).val
        (Matrix.mulVec ((matrixMap z)⁻¹).val v) = v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hv] at h
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_assoc, inv_mul_cancel, mul_one] using (congrArg (fun t => z⁻¹ * t * z) h).symm

omit [Fintype ι] in
theorem row_roots_commute (i j k : ι) (a b : R) :
    Commute (x k i a) (x k j b) := by
  by_cases hi : k = i
  · subst i; simp
  by_cases hj : k = j
  · subst j; simp
  exact x_distant k i k j hj (Ne.symm hi) a b

def rowAddHom (k : ι) : (ι → R) →+ Additive (Group ι R) :=
  AddMonoidHom.noncommPiCoprod (fun i => xAddHom k i) (by
    intro i j _ a b
    exact row_roots_commute i j k a b)

def row (k : ι) (v : ι → R) : Group ι R := (rowAddHom k v).toMul

@[simp] theorem row_single (k i : ι) (a : R) :
    row k (Pi.single i a) = x k i a :=
  congrArg Additive.toMul (AddMonoidHom.noncommPiCoprod_single (fun i => xAddHom k i) i a)

@[simp] theorem row_zero (k : ι) : row k (0 : ι → R) = 1 := (rowAddHom k).map_zero

theorem row_add (k : ι) (v w : ι → R) :
    row k (v + w) = row k v * row k w := (rowAddHom k).map_add v w

def vecMulAddHom (A : Matrix ι ι R) : (ι → R) →+ (ι → R) where
  toFun v := Matrix.vecMul v A
  map_zero' := Matrix.zero_vecMul A
  map_add' := Matrix.add_vecMul A

omit [DecidableEq ι] in
@[simp] theorem vecMulAddHom_apply (A : Matrix ι ι R) (v : ι → R) :
    vecMulAddHom A v = Matrix.vecMul v A := rfl

theorem vecMul_single_matrix (i j : ι) (a : R) (v : ι → R) :
    Matrix.vecMul v (Matrix.single i j a) = Pi.single j (v i * a) := by
  ext l
  by_cases h : j = l
  · subst l; simp [Matrix.vecMul, dotProduct, Matrix.single]
  · simp [Matrix.vecMul, dotProduct, Matrix.single, h]

theorem elementary_inv_vecMul (i j : ι) (h : i ≠ j) (a : R) (v : ι → R) :
    Matrix.vecMul v ((elementary i j h a)⁻¹).val = v + Pi.single j (-(v i * a)) := by
  rw [elementary_inv_val, Matrix.vecMul_sub, Matrix.vecMul_one, vecMul_single_matrix]
  ext l
  by_cases hl : l = j
  · subst l; simp [sub_eq_add_neg]
  · simp [sub_eq_add_neg, Pi.single_eq_of_ne hl]

/-- Row form of the one-root conjugation identity. -/
theorem x_conjugate_row (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a : R) (v : ι → R) :
    x i j a * row k v * (x i j a)⁻¹ =
      row k (Matrix.vecMul v ((elementary i j hij a)⁻¹).val) := by
  have hh : (conjugateAddHom (x i j a)).comp (rowAddHom k) =
      (rowAddHom k).comp (vecMulAddHom ((elementary i j hij a)⁻¹).val) := by
    apply AddMonoidHom.pi_ext
    intro l b
    change x i j a * row k (Pi.single l b) * (x i j a)⁻¹ =
      row k (Matrix.vecMul (Pi.single l b) ((elementary i j hij a)⁻¹).val)
    rw [row_single, elementary_inv_vecMul, row_add, row_single, row_single]
    by_cases hli : l = i
    · subst l
      rw [Pi.single_eq_same]
      calc
        x i j a * x k i b * (x i j a)⁻¹ = ⁅x i j a, x k i b⁆ * x k i b := by
          simp [commutatorElement_def, mul_assoc]
        _ = (⁅x k i b, x i j a⁆)⁻¹ * x k i b := by rw [commutatorElement_inv]
        _ = x k j (-(b * a)) * x k i b := by
          rw [x_chain k i j hik.symm hij hjk.symm, x_neg]
        _ = x k i b * x k j (-(b * a)) :=
          (row_roots_commute j i k (-(b * a)) b).eq
    · rw [Pi.single_eq_of_ne (Ne.symm hli), zero_mul, neg_zero, x_zero, mul_one]
      rw [(x_distant i j k l (Ne.symm hli) hjk a b).eq, mul_inv_cancel_right]
  exact DFunLike.congr_fun hh v

/-- External-row action for arbitrary words omitting k. -/
theorem conjugate_row_of_mem_omitting (k : ι) {z : Group ι R} (hz : z ∈ omitting k)
    (v : ι → R) : z * row k v * z⁻¹ = row k (Matrix.vecMul v ((matrixMap z)⁻¹).val) := by
  induction hz using Subgroup.closure_induction generalizing v with
  | mem z hz =>
    obtain ⟨i, j, a, hik, hjk, rfl⟩ := hz
    by_cases hij : i = j
    · subst j; simp
    rw [x_of_ne i j hij, matrixMap_root, ← x_of_ne i j hij]
    exact x_conjugate_row i j k hij hik hjk a v
  | one => simp
  | mul z w _ _ ihz ihw =>
    simp only [map_mul, mul_inv_rev, Units.val_mul]
    rw [← Matrix.vecMul_vecMul, ← ihz, ← ihw]
    group
  | inv z _ ih =>
    have h := ih (Matrix.vecMul v (matrixMap z).val)
    have hv : Matrix.vecMul (Matrix.vecMul v (matrixMap z).val)
        ((matrixMap z)⁻¹).val = v := by
      rw [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.vecMul_one]
    rw [hv] at h
    simpa only [map_inv, inv_inv, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_assoc, inv_mul_cancel, mul_one] using (congrArg (fun t => z⁻¹ * t * z) h).symm

omit [Ring R] [Ring S] [Fintype ι] [DecidableEq ι] in
theorem commute_commutator {T : Type*} [_root_.Group T] {a b c : T}
    (hb : Commute a b) (hc : Commute a c) : Commute a ⁅b, c⁆ := by
  rw [commutatorElement_def]
  exact ((hb.mul_right hc).mul_right hb.inv_right).mul_right hc.inv_right

/-- A Steinberg element with trivial matrix and an unused index is central.
This is the first centrality statement in the Steinberg kernel argument, with no rank-stability assumption. -/
theorem central_of_omitting (k : ι) {z : Group ι R} (hz : z ∈ omitting k)
    (hπ : matrixMap z = 1) : z ∈ Subgroup.center (Group ι R) := by
  have hc (i : ι) (a : R) : Commute z (x i k a) := by
    have h := conjugate_column_of_mem_omitting k hz (Pi.single i a)
    simp only [hπ, Units.val_one, Matrix.one_mulVec, column_single] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hr (i : ι) (a : R) : Commute z (x k i a) := by
    have h := conjugate_row_of_mem_omitting k hz (Pi.single i a)
    simp only [hπ, inv_one, Units.val_one, Matrix.vecMul_one, row_single] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hx (i j : ι) (hij : i ≠ j) (a : R) : Commute z (root i j hij a) := by
    rw [← x_of_ne i j hij]
    by_cases hik : i = k
    · subst i; exact hr j a
    by_cases hjk : j = k
    · subst j; exact hc i a
    have hchain := x_chain i k j hik (Ne.symm hjk) hij a (1 : R)
    rw [mul_one] at hchain
    rw [← hchain]
    exact commute_commutator (hc i a) (hr j 1)
  rw [Subgroup.mem_center_iff]
  intro w
  have hw : w ∈ Subgroup.centralizer ({z} : Set (Group ι R)) := by
    apply PresentedGroup.generated_by
    rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hx i j hij a).symm.eq
  exact Subgroup.mem_centralizer_singleton_iff.mp hw

end MatrixRepresentation


/-! Orthogonal equivalent corners, as specified by (corner-equivalence)
in the Steinberg kernel argument. The symbol `e` below is the specified d*, not an involution. -/
structure CornerPair (R : Type*) [Ring R] where
  E : R
  F : R
  d : R
  e : R
  E_idem : E * E = E
  F_idem : F * F = F
  EF : E * F = 0
  FE : F * E = 0
  d_support : F * d * E = d
  e_support : E * e * F = e
  ed : e * d = E
  de : d * e = F

namespace CornerPair

variable (c : CornerPair R)

def swap : CornerPair R where
  E := c.F
  F := c.E
  d := c.e
  e := c.d
  E_idem := c.F_idem
  F_idem := c.E_idem
  EF := c.FE
  FE := c.EF
  d_support := c.e_support
  e_support := c.d_support
  ed := c.de
  de := c.ed

theorem d_left : c.F * c.d = c.d := by
  calc
    c.F * c.d = c.F * (c.F * c.d * c.E) := by rw [c.d_support]
    _ = c.F * c.d * c.E := by simp only [← mul_assoc, c.F_idem]
    _ = c.d := c.d_support

theorem d_right : c.d * c.E = c.d := by
  calc
    c.d * c.E = (c.F * c.d * c.E) * c.E := by rw [c.d_support]
    _ = c.F * c.d * c.E := by rw [mul_assoc, c.E_idem]
    _ = c.d := c.d_support

theorem d_left_zero : c.E * c.d = 0 := by
  rw [← c.d_left, ← mul_assoc, c.EF, zero_mul]

theorem d_right_zero : c.d * c.F = 0 := by
  rw [← c.d_right, mul_assoc, c.EF, mul_zero]

theorem e_left : c.E * c.e = c.e := c.swap.d_left

theorem e_right : c.e * c.F = c.e := c.swap.d_right

theorem e_left_zero : c.F * c.e = 0 := c.swap.d_left_zero

theorem e_right_zero : c.e * c.E = 0 := c.swap.d_right_zero

theorem left_of_corner {y : R} (hy : c.E * y * c.E = y) : c.E * y = y := by
  calc
    c.E * y = c.E * (c.E * y * c.E) := by rw [hy]
    _ = c.E * y * c.E := by simp only [← mul_assoc, c.E_idem]
    _ = y := hy

theorem right_of_corner {y : R} (hy : c.E * y * c.E = y) : y * c.E = y := by
  calc
    y * c.E = (c.E * y * c.E) * c.E := by rw [hy]
    _ = c.E * y * c.E := by rw [mul_assoc, c.E_idem]
    _ = y := hy

theorem e_mul_corner {y : R} (hy : c.E * y * c.E = y) : c.e * y = 0 := by
  rw [← c.left_of_corner hy, ← mul_assoc, c.e_right_zero, zero_mul]

theorem corner_mul_d {y : R} (hy : c.E * y * c.E = y) : y * c.d = 0 := by
  rw [← c.right_of_corner hy, mul_assoc, c.d_left_zero, mul_zero]

theorem E_mul_d_corner {y : R} (_hy : c.E * y * c.E = y) : c.E * (c.d * y) = 0 := by
  rw [← mul_assoc, c.d_left_zero, zero_mul]

theorem corner_e_mul_E {y : R} (_hy : c.E * y * c.E = y) : (y * c.e) * c.E = 0 := by
  rw [mul_assoc, c.e_right_zero, mul_zero]

end CornerPair

section Compression
variable [Fintype ι] [DecidableEq ι]

/-- The actual compression word in the Steinberg kernel argument, not a matrix lift assumed to exist. -/
def compression (c : CornerPair R) (p q : ι) : Group ι R :=
  x p q c.d * x q p (-c.e) * x p q c.d

omit [Ring R] [Ring S] [Fintype ι] [DecidableEq ι] in
theorem conjugate_mul {T : Type*} [_root_.Group T] (a b z : T) :
    (a * b) * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹ := by group

theorem compression_column_p (c : CornerPair R) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k)
    (y : R) (hy : c.E * y * c.E = y) :
    compression c p q * x p k y * (compression c p q)⁻¹ = x p k y := by
  rw [← column_single k p y, compression, conjugate_mul, conjugate_mul,
    x_conjugate_column p q k hpq hpk hqk,
    x_conjugate_column q p k hpq.symm hqk hpk,
    x_conjugate_column p q k hpq hpk hqk]
  simp only [elementary_mulVec]
  congr 1
  ext l
  simp [Pi.single_apply, hpq.symm, c.e_mul_corner hy]

theorem compression_column_q (c : CornerPair R) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k)
    (y : R) (hy : c.E * y * c.E = y) :
    compression c p q * x q k y * (compression c p q)⁻¹ = x p k (c.d * y) := by
  rw [← column_single k q y, ← column_single k p (c.d * y), compression,
    conjugate_mul, conjugate_mul,
    x_conjugate_column p q k hpq hpk hqk,
    x_conjugate_column q p k hpq.symm hqk hpk,
    x_conjugate_column p q k hpq hpk hqk]
  simp only [elementary_mulVec]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l
    simp [hpq, hpq.symm, ← mul_assoc, c.ed, c.left_of_corner hy]
  · by_cases hlq : l = q
    · subst l
      simp [hpq, hpq.symm, ← mul_assoc, c.ed, c.left_of_corner hy]
    · simp [Pi.single_apply, hlp, hlq]

theorem compression_row_p (c : CornerPair R) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k)
    (y : R) (hy : c.E * y * c.E = y) :
    compression c p q * x k p y * (compression c p q)⁻¹ = x k p y := by
  rw [← row_single k p y, compression, conjugate_mul, conjugate_mul,
    x_conjugate_row p q k hpq hpk hqk,
    x_conjugate_row q p k hpq.symm hqk hpk,
    x_conjugate_row p q k hpq hpk hqk]
  simp only [elementary_inv_vecMul]
  congr 1
  ext l
  simp [Pi.single_apply, hpq.symm, c.corner_mul_d hy]

theorem compression_row_q (c : CornerPair R) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k)
    (y : R) (hy : c.E * y * c.E = y) :
    compression c p q * x k q y * (compression c p q)⁻¹ = x k p (y * c.e) := by
  rw [← row_single k q y, ← row_single k p (y * c.e), compression,
    conjugate_mul, conjugate_mul,
    x_conjugate_row p q k hpq hpk hqk,
    x_conjugate_row q p k hpq.symm hqk hpk,
    x_conjugate_row p q k hpq hpk hqk]
  simp only [elementary_inv_vecMul]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l
    simp [hpq, mul_assoc, c.ed, c.right_of_corner hy]
  · by_cases hlq : l = q
    · subst l
      simp [hpq, hpq.symm, mul_assoc, c.ed, c.right_of_corner hy]
    · simp [Pi.single_apply, hlp, hlq]

/-- Subgroup generated by root coefficients in an idempotent corner. -/
def cornerSubgroup (E : R) : Subgroup (Group ι R) :=
  Subgroup.closure {z | ∃ i j y, E * y * E = y ∧ z = x i j y}

omit [Fintype ι] [DecidableEq ι] in
theorem commutator_mem_subgroup (K : Subgroup (Group ι R)) {a b : Group ι R}
    (ha : a ∈ K) (hb : b ∈ K) : ⁅a, b⁆ ∈ K := by
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

/-- Compression sends all corner words into the subgroup with an unused index. -/
theorem compression_mem_omitting (c : CornerPair R) (p q r : ι)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {z : Group ι R} (hz : z ∈ cornerSubgroup c.E) :
    compression c p q * z * (compression c p q)⁻¹ ∈ omitting q := by
  let C := (MulAut.conj (compression c p q)).toMonoidHom
  have hle : cornerSubgroup c.E ≤ (omitting q).comap C := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, j, y, hy, rfl⟩
    change C (x i j y) ∈ omitting q
    by_cases hij : i = j
    · subst j; simp
    by_cases hip : i = p
    · subst i
      by_cases hjq : j = q
      · subst j
        have hroot : x p q y = ⁅x p r y, x r q c.E⁆ := by
          rw [x_chain p r q hpr hqr.symm hpq, c.right_of_corner hy]
        rw [hroot, map_commutatorElement]
        change ⁅compression c p q * x p r y * (compression c p q)⁻¹,
          compression c p q * x r q c.E * (compression c p q)⁻¹⁆ ∈ omitting q
        rw [compression_column_p c p q r hpq hpr hqr y hy,
          compression_row_q c p q r hpq hpr hqr c.E (by rw [c.E_idem, c.E_idem])]
        exact commutator_mem_subgroup _ (x_mem_omitting _ _ _ hpq hqr.symm _)
          (x_mem_omitting _ _ _ hqr.symm hpq _)
      · change compression c p q * x p j y * (compression c p q)⁻¹ ∈ omitting q
        rw [compression_column_p c p q j hpq hij (Ne.symm hjq) y hy]
        exact x_mem_omitting _ _ _ hpq hjq _
    by_cases hiq : i = q
    · subst i
      by_cases hjp : j = p
      · subst j
        have hroot : x q p y = ⁅x q r y, x r p c.E⁆ := by
          rw [x_chain q r p hqr hpr.symm hpq.symm, c.right_of_corner hy]
        rw [hroot, map_commutatorElement]
        change ⁅compression c p q * x q r y * (compression c p q)⁻¹,
          compression c p q * x r p c.E * (compression c p q)⁻¹⁆ ∈ omitting q
        rw [compression_column_q c p q r hpq hpr hqr y hy,
          compression_row_p c p q r hpq hpr hqr c.E (by rw [c.E_idem, c.E_idem])]
        exact commutator_mem_subgroup _ (x_mem_omitting _ _ _ hpq hqr.symm _)
          (x_mem_omitting _ _ _ hqr.symm hpq _)
      · change compression c p q * x q j y * (compression c p q)⁻¹ ∈ omitting q
        rw [compression_column_q c p q j hpq (Ne.symm hjp) hij y hy]
        exact x_mem_omitting _ _ _ hpq (Ne.symm hij) _
    by_cases hjp : j = p
    · subst j
      change compression c p q * x i p y * (compression c p q)⁻¹ ∈ omitting q
      rw [compression_row_p c p q i hpq (Ne.symm hip) (Ne.symm hiq) y hy]
      exact x_mem_omitting _ _ _ hiq hpq _
    by_cases hjq : j = q
    · subst j
      change compression c p q * x i q y * (compression c p q)⁻¹ ∈ omitting q
      rw [compression_row_q c p q i hpq (Ne.symm hip) (Ne.symm hiq) y hy]
      exact x_mem_omitting _ _ _ hiq hpq _
    have h₁ := x_distant p q i j (Ne.symm hjp) (Ne.symm hiq) c.d y
    have h₂ := x_distant q p i j (Ne.symm hjq) (Ne.symm hip) (-c.e) y
    have hW : Commute (compression c p q) (x i j y) := (h₁.mul_left h₂).mul_left h₁
    change compression c p q * x i j y * (compression c p q)⁻¹ ∈ omitting q
    rw [hW.eq, mul_inv_cancel_right]
    exact x_mem_omitting _ _ _ hiq hjq _
  exact hle hz

/-- the Steinberg kernel argument, corner-centrality. No relation for opposite roots is assumed. -/
theorem central_of_corner (c : CornerPair R) (p q r : ι)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {z : Group ι R} (hz : z ∈ cornerSubgroup c.E) (hπ : matrixMap z = 1) :
    z ∈ Subgroup.center (Group ι R) := by
  have hc := central_of_omitting q
    (compression_mem_omitting c p q r hpq hpr hqr hz)
    (by simp [hπ])
  have hn := (inferInstance : (Subgroup.center (Group ι R)).Normal).conj_mem
    _ hc (compression c p q)⁻¹
  simpa only [inv_inv, inv_mul_cancel_left, mul_inv_cancel_right, mul_assoc,
    inv_mul_cancel, one_mul, mul_one] using hn

end Compression

section OrthogonalCorners
variable [DecidableEq ι]

theorem x_commute_of_zero_nonopposite (i j k l : ι) (a b : R)
    (hab : a * b = 0) (hba : b * a = 0) (hnot : i ≠ l ∨ j ≠ k) :
    Commute (x i j a) (x k l b) := by
  by_cases hij : i = j
  · subst j; simp
  by_cases hkl : k = l
  · subst l; simp
  by_cases hjk : j = k
  · subst k
    have hil : i ≠ l := hnot.resolve_right (not_not_intro rfl)
    apply commutatorElement_eq_one_iff_commute.mp
    rw [x_chain i j l hij hkl hil, hab, x_zero]
  by_cases hil : i = l
  · subst l
    apply Commute.symm
    apply commutatorElement_eq_one_iff_commute.mp
    rw [x_chain k i j hkl hij (Ne.symm hjk), hba, x_zero]
  exact x_distant i j k l hil hjk a b

omit [DecidableEq ι] in
theorem corner_product_zero {E F a b : R} (hEF : E * F = 0)
    (ha : E * a * E = a) (hb : F * b * F = b) : a * b = 0 := by
  calc
    a * b = (E * a * E) * (F * b * F) := by rw [ha, hb]
    _ = E * a * (E * F) * b * F := by noncomm_ring
    _ = 0 := by rw [hEF]; simp

/-- Opposite roots also commute for orthogonal corner coefficients; this follows
from a third root index, not from an additional Steinberg defining relation. -/
theorem x_commute_orthogonal_corners
    (hthird : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {E F : R} (hE : E * E = E) (hEF : E * F = 0) (hFE : F * E = 0)
    (i j k l : ι) (a b : R) (ha : E * a * E = a) (hb : F * b * F = b) :
    Commute (x i j a) (x k l b) := by
  have hab := corner_product_zero hEF ha hb
  have hba := corner_product_zero hFE hb ha
  by_cases hij : i = j
  · subst j; simp
  by_cases hil : i = l
  · subst l
    by_cases hjk : j = k
    · subst k
      obtain ⟨r, hri, hrj⟩ := hthird i j
      have haE : a * E = a := by
        calc
          a * E = (E * a * E) * E := by rw [ha]
          _ = a := by rw [mul_assoc, hE, ha]
      have hEb : E * b = 0 := by
        calc
          E * b = E * (F * b * F) := by rw [hb]
          _ = 0 := by simp only [← mul_assoc, hEF, zero_mul]
      have hbE : b * E = 0 := by
        calc
          b * E = (F * b * F) * E := by rw [hb]
          _ = 0 := by simp only [mul_assoc, hFE, mul_zero]
      have hx : x i j a = ⁅x i r a, x r j E⁆ := by
        rw [x_chain i r j (Ne.symm hri) hrj hij, haE]
      rw [hx]
      apply Commute.symm
      apply commute_commutator
      · exact (x_commute_of_zero_nonopposite i r j i a b hab hba (Or.inr hrj)).symm
      · exact (x_commute_of_zero_nonopposite r j j i E b hEb hbE (Or.inl hri)).symm
    · exact x_commute_of_zero_nonopposite i j k i a b hab hba (Or.inr hjk)
  · exact x_commute_of_zero_nonopposite i j k l a b hab hba (Or.inl hil)

/-- the Steinberg kernel argument, orthogonal-root-images, extended from roots to all words. -/
theorem cornerSubgroups_commute
    (hthird : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    {E F : R} (hE : E * E = E) (hEF : E * F = 0) (hFE : F * E = 0)
    {z w : Group ι R} (hz : z ∈ cornerSubgroup E) (hw : w ∈ cornerSubgroup F) :
    Commute z w := by
  induction hz using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨i, j, a, ha, rfl⟩ := hz
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨k, l, b, hb, rfl⟩ := hw
      exact x_commute_orthogonal_corners hthird hE hEF hFE i j k l a b ha hb
    | one => exact Commute.one_right _
    | mul _ _ _ _ ih₁ ih₂ => exact ih₁.mul_right ih₂
    | inv _ _ ih => exact ih.inv_right
  | one => exact Commute.one_left _
  | mul _ _ _ _ ih₁ ih₂ => exact ih₁.mul_left ih₂
  | inv _ _ ih => exact ih.inv_left

end OrthogonalCorners

section BalancedDiagonal
variable [Fintype ι] [DecidableEq ι]

/-- Weyl word for an involutive unit b=b⁻¹. -/
def weyl (b : R) (p q : ι) : Group ι R :=
  x p q b * x q p (-b) * x p q b

theorem weyl_column_p (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    weyl b p q * x p k y * (weyl b p q)⁻¹ = x q k (-(b * y)) := by
  rw [← column_single k p y, ← column_single k q (-(b * y)), weyl,
    conjugate_mul, conjugate_mul,
    x_conjugate_column p q k hpq hpk hqk,
    x_conjugate_column q p k hpq.symm hqk hpk,
    x_conjugate_column p q k hpq hpk hqk]
  simp only [elementary_mulVec]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l; simp [hpq.symm, ← mul_assoc, hb]
  · by_cases hlq : l = q
    · subst l; simp [hpq.symm, ← mul_assoc, hb]
    · simp [Pi.single_apply, hlp, hlq]

theorem weyl_column_q (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    weyl b p q * x q k y * (weyl b p q)⁻¹ = x p k (b * y) := by
  rw [← column_single k q y, ← column_single k p (b * y), weyl,
    conjugate_mul, conjugate_mul,
    x_conjugate_column p q k hpq hpk hqk,
    x_conjugate_column q p k hpq.symm hqk hpk,
    x_conjugate_column p q k hpq hpk hqk]
  simp only [elementary_mulVec]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l; simp [hpq, hpq.symm, ← mul_assoc, hb]
  · by_cases hlq : l = q
    · subst l; simp [hpq, hpq.symm, ← mul_assoc, hb]
    · simp [Pi.single_apply, hlp, hlq]

theorem weyl_row_p (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    weyl b p q * x k p y * (weyl b p q)⁻¹ = x k q (-(y * b)) := by
  rw [← row_single k p y, ← row_single k q (-(y * b)), weyl,
    conjugate_mul, conjugate_mul,
    x_conjugate_row p q k hpq hpk hqk,
    x_conjugate_row q p k hpq.symm hqk hpk,
    x_conjugate_row p q k hpq hpk hqk]
  simp only [elementary_inv_vecMul]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l; simp [hpq, hpq.symm, mul_assoc, hb]
  · by_cases hlq : l = q
    · subst l; simp [hpq, hpq.symm, mul_assoc, hb]
    · simp [Pi.single_apply, hlp, hlq]

theorem weyl_row_q (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    weyl b p q * x k q y * (weyl b p q)⁻¹ = x k p (y * b) := by
  rw [← row_single k q y, ← row_single k p (y * b), weyl,
    conjugate_mul, conjugate_mul,
    x_conjugate_row p q k hpq hpk hqk,
    x_conjugate_row q p k hpq.symm hqk hpk,
    x_conjugate_row p q k hpq hpk hqk]
  simp only [elementary_inv_vecMul]
  congr 1
  ext l
  by_cases hlp : l = p
  · subst l; simp [hpq, mul_assoc, hb]
  · by_cases hlq : l = q
    · subst l; simp [hpq, hpq.symm, mul_assoc, hb]
    · simp [Pi.single_apply, hlp, hlq]

def balanced (b : R) (p q : ι) : Group ι R := weyl b p q * weyl (-1) p q

theorem balanced_column_p (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    balanced b p q * x p k y * (balanced b p q)⁻¹ = x p k (b * y) := by
  rw [balanced, conjugate_mul, weyl_column_p (-1) (by simp) p q k hpq hpk hqk,
    weyl_column_q b hb p q k hpq hpk hqk]
  simp

theorem balanced_column_q (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    balanced b p q * x q k y * (balanced b p q)⁻¹ = x q k (b * y) := by
  rw [balanced, conjugate_mul, weyl_column_q (-1) (by simp) p q k hpq hpk hqk,
    weyl_column_p b hb p q k hpq hpk hqk]
  simp

theorem balanced_row_p (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    balanced b p q * x k p y * (balanced b p q)⁻¹ = x k p (y * b) := by
  rw [balanced, conjugate_mul, weyl_row_p (-1) (by simp) p q k hpq hpk hqk,
    weyl_row_q b hb p q k hpq hpk hqk]
  simp

theorem balanced_row_q (b : R) (hb : b * b = 1) (p q k : ι)
    (hpq : p ≠ q) (hpk : p ≠ k) (hqk : q ≠ k) (y : R) :
    balanced b p q * x k q y * (balanced b p q)⁻¹ = x k q (y * b) := by
  rw [balanced, conjugate_mul, weyl_row_q (-1) (by simp) p q k hpq hpk hqk,
    weyl_row_p b hb p q k hpq hpk hqk]
  simp

def pairScalar (b : R) (p q i : ι) : R := if i = p ∨ i = q then b else 1

/-- Exact balanced diagonal action, including the roots internal to its pair. -/
theorem balanced_root (b : R) (hb : b * b = 1)
    (hthird : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    (p q : ι) (hpq : p ≠ q) (i j : ι) (y : R) :
    balanced b p q * x i j y * (balanced b p q)⁻¹ =
      x i j (pairScalar b p q i * y * pairScalar b p q j) := by
  by_cases hij : i = j
  · subst j; simp
  by_cases hip : i = p
  · subst i
    by_cases hjq : j = q
    · subst j
      obtain ⟨r, hrp, hrq⟩ := hthird p q
      have hroot : x p q y = ⁅x p r y, x r q (1 : R)⁆ := by
        rw [x_chain p r q (Ne.symm hrp) hrq hpq, mul_one]
      rw [hroot]
      change (MulAut.conj (balanced b p q)) ⁅x p r y, x r q (1 : R)⁆ = _
      rw [map_commutatorElement]
      simp only [MulAut.conj_apply]
      rw [balanced_column_p b hb p q r hpq (Ne.symm hrp) (Ne.symm hrq),
        balanced_row_q b hb p q r hpq (Ne.symm hrp) (Ne.symm hrq),
        x_chain p r q (Ne.symm hrp) hrq hpq]
      simp [pairScalar]
    · simpa [pairScalar, Ne.symm hij, hjq] using
        balanced_column_p b hb p q j hpq hij (Ne.symm hjq) y
  by_cases hiq : i = q
  · subst i
    by_cases hjp : j = p
    · subst j
      obtain ⟨r, hrp, hrq⟩ := hthird p q
      have hroot : x q p y = ⁅x q r y, x r p (1 : R)⁆ := by
        rw [x_chain q r p (Ne.symm hrq) hrp hpq.symm, mul_one]
      rw [hroot]
      change (MulAut.conj (balanced b p q)) ⁅x q r y, x r p (1 : R)⁆ = _
      rw [map_commutatorElement]
      simp only [MulAut.conj_apply]
      rw [balanced_column_q b hb p q r hpq (Ne.symm hrp) (Ne.symm hrq),
        balanced_row_p b hb p q r hpq (Ne.symm hrp) (Ne.symm hrq),
        x_chain q r p (Ne.symm hrq) hrp hpq.symm]
      simp [pairScalar]
    · simpa [pairScalar, Ne.symm hij, hjp] using
        balanced_column_q b hb p q j hpq (Ne.symm hjp) hij y
  by_cases hjp : j = p
  · subst j
    simpa [pairScalar, hip, hiq] using
      balanced_row_p b hb p q i hpq (Ne.symm hip) (Ne.symm hiq) y
  by_cases hjq : j = q
  · subst j
    simpa [pairScalar, hip, hiq] using
      balanced_row_q b hb p q i hpq (Ne.symm hip) (Ne.symm hiq) y
  have hc (a : R) : Commute (weyl a p q) (x i j y) := by
    have h₁ := x_distant p q i j (Ne.symm hjp) (Ne.symm hiq) a y
    have h₂ := x_distant q p i j (Ne.symm hjq) (Ne.symm hip) (-a) y
    exact (h₁.mul_left h₂).mul_left h₁
  have hD : Commute (balanced b p q) (x i j y) := (hc b).mul_left (hc (-1))
  rw [hD.eq, mul_inv_cancel_right]
  simp [pairScalar, hip, hiq, hjp, hjq]

/-- Scalar diagonal lift in rank six, exactly the three factors in the source. -/
def scalarDiagonal (b : R) : Group (Fin 6) R :=
  balanced b 0 1 * balanced b 2 3 * balanced b 4 5

omit [Fintype ι] [DecidableEq ι] in
theorem scalarDiagonal_root (b : R) (hb : b * b = 1) (i j : Fin 6) (y : R) :
    scalarDiagonal b * x i j y * (scalarDiagonal b)⁻¹ = x i j (b * y * b) := by
  have ht : ∀ s t : Fin 6, ∃ k, k ≠ s ∧ k ≠ t :=
    fun s t => Fin.exists_ne_and_ne_of_two_lt s t (by decide)
  rw [scalarDiagonal, conjugate_mul, conjugate_mul,
    balanced_root b hb ht 4 5 (by decide),
    balanced_root b hb ht 2 3 (by decide),
    balanced_root b hb ht 0 1 (by decide)]
  have hleft (t : Fin 6) :
      pairScalar b 0 1 t * pairScalar b 2 3 t * pairScalar b 4 5 t = b := by
    fin_cases t <;> simp [pairScalar]
  have hright (t : Fin 6) :
      pairScalar b 4 5 t * pairScalar b 2 3 t * pairScalar b 0 1 t = b := by
    fin_cases t <;> simp [pairScalar]
  congr 1
  calc
    _ = (pairScalar b 0 1 i * pairScalar b 2 3 i * pairScalar b 4 5 i) * y *
        (pairScalar b 4 5 j * pairScalar b 2 3 j * pairScalar b 0 1 j) := by
      simp only [mul_assoc]
    _ = b * y * b := by rw [hleft, hright]

end BalancedDiagonal

namespace CornerPair
variable (c : CornerPair R)

theorem dd : c.d * c.d = 0 := by
  calc
    c.d * c.d = (c.d * c.E) * c.d := by rw [c.d_right]
    _ = 0 := by rw [mul_assoc, c.d_left_zero, mul_zero]

theorem ee : c.e * c.e = 0 := c.swap.dd

/-- The involutive scalar interchanging the two corners. -/
def swapScalar : R := c.d + c.e + 1 - c.E - c.F

theorem swapScalar_square : c.swapScalar * c.swapScalar = 1 := by
  simp only [swapScalar, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    c.dd, c.ee, c.ed, c.de, c.E_idem, c.F_idem, c.EF, c.FE, c.d_left,
    c.d_right, c.d_left_zero, c.d_right_zero, c.e_left, c.e_right,
    c.e_left_zero, c.e_right_zero]
  abel

theorem swapScalar_E : c.swapScalar * c.E = c.d := by
  simp only [swapScalar, add_mul, sub_mul, one_mul, c.d_right, c.e_right_zero,
    c.E_idem, c.FE]
  abel

theorem d_swapScalar : c.d * c.swapScalar = c.F := by
  simp only [swapScalar, mul_add, mul_sub, mul_one, c.dd, c.de,
    c.d_right, c.d_right_zero]
  abel

theorem swapScalar_E_swapScalar : c.swapScalar * c.E * c.swapScalar = c.F := by
  rw [c.swapScalar_E, c.d_swapScalar]

theorem swapScalar_commute {a : R} (hE : Commute c.E a) (hF : Commute c.F a)
    (hd : Commute c.d a) (he : Commute c.e a) : Commute c.swapScalar a :=
  (((hd.add_left he).add_left (Commute.one_left a)).sub_left hE).sub_left hF

end CornerPair

/-- Cutting down a nonunital coefficient map by a commuting idempotent. -/
def cornerMap (ψ : R →ₙ+* S) (E : S) (hE : E * E = E)
    (hc : ∀ a, Commute E (ψ a)) : R →ₙ+* S where
  toFun a := ψ a * E
  map_zero' := by simp
  map_add' a b := by simp [add_mul]
  map_mul' a b := by
    rw [map_mul]
    calc
      ψ a * ψ b * E = ψ a * ψ b * (E * E) := by rw [hE]
      _ = ψ a * (ψ b * E) * E := by simp only [mul_assoc]
      _ = ψ a * (E * ψ b) * E := by rw [(hc b).eq]
      _ = ψ a * E * (ψ b * E) := by simp only [mul_assoc]

@[simp] theorem cornerMap_apply (ψ : R →ₙ+* S) (E : S) (hE : E * E = E)
    (hc : ∀ a, Commute E (ψ a)) (a : R) : cornerMap ψ E hE hc a = ψ a * E := rfl

theorem cornerMap_corner (ψ : R →ₙ+* S) (E : S) (hE : E * E = E)
    (hc : ∀ a, Commute E (ψ a)) (a : R) :
    E * cornerMap ψ E hE hc a * E = cornerMap ψ E hE hc a := by
  simp only [cornerMap_apply]
  rw [← mul_assoc E, (hc a).eq]
  simp only [mul_assoc, hE]

section CornerImages
variable [DecidableEq ι]

theorem coefficientMap_mem_corner (ψ : R →ₙ+* S) (E : S) (hE : E * E = E)
    (hc : ∀ a, Commute E (ψ a)) (z : Group ι R) :
    coefficientMap (cornerMap ψ E hE hc) z ∈ cornerSubgroup E := by
  change z ∈ (cornerSubgroup E).comap (coefficientMap (cornerMap ψ E hE hc))
  apply PresentedGroup.generated_by
  rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
  change coefficientMap (cornerMap ψ E hE hc) (root i j hij a) ∈ cornerSubgroup E
  rw [coefficientMap_root, ← x_of_ne i j hij]
  exact Subgroup.subset_closure ⟨i, j, _, cornerMap_corner ψ E hE hc a, rfl⟩

/-- Centrality of every corner image of an arbitrary matrix-kernel element. -/
theorem coefficientMap_corner_central (ψ : R →ₙ+* S) (c : CornerPair S)
    (hE : ∀ a, Commute c.E (ψ a)) (p q r : ι)
    [Fintype ι] (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {z : Group ι R} (hz : matrixMap z = 1) :
    coefficientMap (cornerMap ψ c.E c.E_idem hE) z ∈ Subgroup.center (Group ι S) :=
  central_of_corner c p q r hpq hpr hqr
    (coefficientMap_mem_corner ψ c.E c.E_idem hE z)
    (coefficientMap_preserves_kernel _ z hz)

end CornerImages

/-- the Steinberg kernel argument, corner-comparison, with exact group elements rather than K₂ classes. -/
theorem corner_comparison (ψ : R →ₙ+* S) (c : CornerPair S)
    (hE : ∀ a, Commute c.E (ψ a)) (hF : ∀ a, Commute c.F (ψ a))
    (hd : ∀ a, Commute c.d (ψ a)) (he : ∀ a, Commute c.e (ψ a))
    {z : Group (Fin 6) R} (hz : matrixMap z = 1) :
    coefficientMap (cornerMap ψ c.E c.E_idem hE) z =
      coefficientMap (cornerMap ψ c.F c.F_idem hF) z := by
  let D := scalarDiagonal c.swapScalar
  have hmaps : ((MulAut.conj D).toMonoidHom).comp
      (coefficientMap (cornerMap ψ c.E c.E_idem hE)) =
      coefficientMap (cornerMap ψ c.F c.F_idem hF) := by
    apply PresentedGroup.ext
    rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
    change D * coefficientMap _ (root i j hij a) * D⁻¹ =
      coefficientMap _ (root i j hij a)
    rw [coefficientMap_root, coefficientMap_root, ← x_of_ne i j hij,
      ← x_of_ne i j hij]
    rw [scalarDiagonal_root c.swapScalar c.swapScalar_square]
    congr 1
    simp only [cornerMap_apply]
    calc
      c.swapScalar * (ψ a * c.E) * c.swapScalar =
          ψ a * (c.swapScalar * c.E * c.swapScalar) := by
        rw [← mul_assoc c.swapScalar, (c.swapScalar_commute (hE a) (hF a) (hd a) (he a)).eq]
        simp only [mul_assoc]
      _ = ψ a * c.F := by rw [c.swapScalar_E_swapScalar]
  have hcentral := coefficientMap_corner_central ψ c hE (0 : Fin 6) 1 2
    (by decide) (by decide) (by decide) hz
  have hc := Subgroup.mem_center_iff.mp hcentral D
  have h := DFunLike.congr_fun hmaps z
  change D * coefficientMap _ z * D⁻¹ = coefficientMap _ z at h
  rw [hc, mul_inv_cancel_right] at h
  exact h

theorem orthogonal_sum_idem {E F : S} (hE : E * E = E) (hF : F * F = F)
    (hEF : E * F = 0) (hFE : F * E = 0) : (E + F) * (E + F) = E + F := by
  simp only [add_mul, mul_add, hE, hF, hEF, hFE, zero_add, add_zero]

/-- Orthogonal corner images split without any residual central factor. -/
theorem coefficientMap_corner_sum [DecidableEq ι]
    (hthird : ∀ i j : ι, ∃ k, k ≠ i ∧ k ≠ j)
    (ψ : R →ₙ+* S) (E F : S) (hE : E * E = E) (hF : F * F = F)
    (hEF : E * F = 0) (hFE : F * E = 0)
    (hcE : ∀ a, Commute E (ψ a)) (hcF : ∀ a, Commute F (ψ a)) (z : Group ι R) :
    coefficientMap (cornerMap ψ (E + F) (orthogonal_sum_idem hE hF hEF hFE)
      (fun a => (hcE a).add_left (hcF a))) z =
      coefficientMap (cornerMap ψ E hE hcE) z *
        coefficientMap (cornerMap ψ F hF hcF) z := by
  let fE := coefficientMap (ι := ι) (cornerMap ψ E hE hcE)
  let fF := coefficientMap (ι := ι) (cornerMap ψ F hF hcF)
  have hc (v w : Group ι R) : Commute (fE v) (fF w) :=
    cornerSubgroups_commute hthird hE hEF hFE
      (coefficientMap_mem_corner ψ E hE hcE v)
      (coefficientMap_mem_corner ψ F hF hcF w)
  let f : Group ι R →* Group ι S := {
    toFun := fun v => fE v * fF v
    map_one' := by simp
    map_mul' := fun v w => by
      simp only [map_mul]
      calc
        fE v * fE w * (fF v * fF w) = fE v * (fE w * fF v) * fF w := by group
        _ = fE v * (fF v * fE w) * fF w := by rw [(hc w v).eq]
        _ = fE v * fF v * (fE w * fF w) := by group }
  have hmaps : coefficientMap (ι := ι)
      (cornerMap ψ (E + F) (orthogonal_sum_idem hE hF hEF hFE)
        (fun a => (hcE a).add_left (hcF a))) = f := by
    apply PresentedGroup.ext
    rintro ⟨⟨⟨i, j⟩, hij⟩, a⟩
    change coefficientMap _ (root i j hij a) =
      coefficientMap _ (root i j hij a) * coefficientMap _ (root i j hij a)
    simp only [coefficientMap_root, cornerMap_apply, mul_add, root_add]
  exact DFunLike.congr_fun hmaps z

/-- A pair of supported one-sided inverse elements, with the prescribed
commutation with the nonunital coefficient image. -/
structure SupportedPair (ψ : R →ₙ+* S) where
  U : S
  V : S
  VU : V * U = ψ 1
  PU : ψ 1 * U = U
  UP : U * ψ 1 = U
  PV : ψ 1 * V = V
  VP : V * ψ 1 = V
  commU : ∀ a, Commute U (ψ a)
  commV : ∀ a, Commute V (ψ a)

namespace SupportedPair
variable {ψ : R →ₙ+* S} (p q : SupportedPair ψ)

def E : S := p.U * p.V

theorem E_idem : p.E * p.E = p.E := by
  change (p.U * p.V) * (p.U * p.V) = p.U * p.V
  calc
    _ = p.U * (p.V * p.U) * p.V := by simp only [mul_assoc]
    _ = p.U * p.V := by rw [p.VU, p.UP]

theorem commE (a : R) : Commute p.E (ψ a) := (p.commU a).mul_left (p.commV a)

/-- Composition gives the descendants 00 and 01 of the zero corner. -/
def comp : SupportedPair ψ where
  U := p.U * q.U
  V := q.V * p.V
  VU := by
    calc
      q.V * p.V * (p.U * q.U) = q.V * (p.V * p.U) * q.U := by simp only [mul_assoc]
      _ = ψ 1 := by rw [p.VU, q.VP, q.VU]
  PU := by rw [← mul_assoc, p.PU]
  UP := by rw [mul_assoc, q.UP]
  PV := by rw [← mul_assoc, q.PV]
  VP := by rw [mul_assoc, p.VP]
  commU a := (p.commU a).mul_left (q.commU a)
  commV a := (q.commV a).mul_left (p.commV a)

theorem E_mul_E (hpq : p.V * q.U = 0) : p.E * q.E = 0 := by
  change (p.U * p.V) * (q.U * q.V) = 0
  calc
    _ = p.U * (p.V * q.U) * q.V := by simp only [mul_assoc]
    _ = 0 := by rw [hpq]; simp

/-- Explicit equivalence data between two orthogonal supported corners. -/
def corners (hpq : p.V * q.U = 0) (hqp : q.V * p.U = 0) : CornerPair S where
  E := p.E
  F := q.E
  d := q.U * p.V
  e := p.U * q.V
  E_idem := p.E_idem
  F_idem := q.E_idem
  EF := p.E_mul_E q hpq
  FE := q.E_mul_E p hqp
  d_support := by
    change (q.U * q.V) * (q.U * p.V) * (p.U * p.V) = q.U * p.V
    calc
      _ = q.U * (q.V * q.U) * (p.V * p.U) * p.V := by simp only [mul_assoc]
      _ = q.U * p.V := by rw [q.VU, p.VU, q.UP, q.UP]
  e_support := by
    change (p.U * p.V) * (p.U * q.V) * (q.U * q.V) = p.U * q.V
    calc
      _ = p.U * (p.V * p.U) * (q.V * q.U) * q.V := by simp only [mul_assoc]
      _ = p.U * q.V := by rw [p.VU, q.VU, p.UP, p.UP]
  ed := by
    change (p.U * q.V) * (q.U * p.V) = p.U * p.V
    calc
      _ = p.U * (q.V * q.U) * p.V := by simp only [mul_assoc]
      _ = p.U * p.V := by rw [q.VU, p.UP]
  de := by
    change (q.U * p.V) * (p.U * q.V) = q.U * q.V
    calc
      _ = q.U * (p.V * p.U) * q.V := by simp only [mul_assoc]
      _ = q.U * q.V := by rw [p.VU, q.UP]

def image : Group (Fin 6) R →* Group (Fin 6) S :=
  coefficientMap (cornerMap ψ p.E p.E_idem p.commE)

theorem image_eq (hpq : p.V * q.U = 0) (hqp : q.V * p.U = 0)
    {z : Group (Fin 6) R} (hz : matrixMap z = 1) : p.image z = q.image z :=
  corner_comparison ψ (p.corners q hpq hqp) p.commE q.commE
    (fun a => (q.commU a).mul_left (p.commV a))
    (fun a => (p.commU a).mul_left (q.commV a)) hz

theorem comp_cross (r : SupportedPair ψ) : (p.comp q).V * (p.comp r).U = q.V * r.U := by
  change (q.V * p.V) * (p.U * r.U) = q.V * r.U
  calc
    _ = q.V * (p.V * p.U) * r.U := by simp only [mul_assoc]
    _ = q.V * r.U := by rw [p.VU, q.VP]

theorem comp_cross_right (r : SupportedPair ψ) (hpq : p.V * q.U = 0) :
    (p.comp r).V * q.U = 0 := by
  change (r.V * p.V) * q.U = 0
  rw [mul_assoc, hpq, mul_zero]

theorem comp_cross_left (r : SupportedPair ψ) (hqp : q.V * p.U = 0) :
    q.V * (p.comp r).U = 0 := by
  change q.V * (p.U * r.U) = 0
  rw [← mul_assoc, hqp, zero_mul]

theorem comp_split (hsum : p.E + q.E = ψ 1) :
    (p.comp p).E + (p.comp q).E = p.E := by
  calc
    (p.comp p).E + (p.comp q).E = p.U * (p.E + q.E) * p.V := by
      dsimp [comp, E]
      noncomm_ring
    _ = p.E := by rw [hsum, p.UP]; rfl

theorem image_split (r : SupportedPair ψ) (hsum : q.E + r.E = p.E)
    (hqr : q.V * r.U = 0) (hrq : r.V * q.U = 0) (z : Group (Fin 6) R) :
    p.image z = q.image z * r.image z := by
  have hqrE := q.E_mul_E r hqr
  have hrqE := r.E_mul_E q hrq
  have hm : cornerMap ψ p.E p.E_idem p.commE =
      cornerMap ψ (q.E + r.E) (orthogonal_sum_idem q.E_idem r.E_idem hqrE hrqE)
        (fun a => (q.commE a).add_left (r.commE a)) := by
    ext a
    simp only [cornerMap_apply, hsum]
  change coefficientMap _ z = _
  rw [hm]
  exact coefficientMap_corner_sum
    (fun i j => Fin.exists_ne_and_ne_of_two_lt i j (by decide))
    ψ q.E r.E q.E_idem r.E_idem hqrE hrqE q.commE r.commE z

/-- The source four-corner swindle. All comparison and commutation facts above
hold in St₆ itself, so the final cancellation is an equality of group elements. -/
theorem annihilation (hpq : p.V * q.U = 0) (hqp : q.V * p.U = 0)
    (hsum : p.E + q.E = ψ 1) {z : Group (Fin 6) R} (hz : matrixMap z = 1) :
    coefficientMap ψ z = 1 := by
  have heq := p.image_eq q hpq hqp hz
  have h00 := (p.comp p).image_eq q (p.comp_cross_right q p hpq)
    (p.comp_cross_left q p hqp) hz
  have h01 := (p.comp q).image_eq q (p.comp_cross_right q q hpq)
    (p.comp_cross_left q q hqp) hz
  have hchildren : p.image z = (p.comp p).image z * (p.comp q).image z :=
    p.image_split (p.comp p) (p.comp q) (p.comp_split q hsum)
      (by rw [p.comp_cross p q, hpq]) (by rw [p.comp_cross q p, hqp]) z
  rw [h00, h01, ← heq] at hchildren
  have hpone : p.image z = 1 := by
    have h : p.image z * 1 = p.image z * p.image z := by simpa using hchildren
    exact (mul_left_cancel h).symm
  have hqone : q.image z = 1 := heq ▸ hpone
  have hmaps : cornerMap ψ (p.E + q.E)
      (orthogonal_sum_idem p.E_idem q.E_idem (p.E_mul_E q hpq) (q.E_mul_E p hqp))
      (fun a => (p.commE a).add_left (q.commE a)) = ψ := by
    ext a
    simp only [cornerMap_apply, hsum, ← map_mul, mul_one]
  have hsplit := coefficientMap_corner_sum
    (fun i j : Fin 6 => Fin.exists_ne_and_ne_of_two_lt i j (by decide))
    ψ p.E q.E p.E_idem q.E_idem (p.E_mul_E q hpq) (q.E_mul_E p hqp)
    p.commE q.commE z
  rw [hmaps] at hsplit
  change coefficientMap ψ z = p.image z * q.image z at hsplit
  simpa only [hpone, hqone, one_mul] using hsplit

end SupportedPair

/-- Elementary support calculus for the corner ψ(1)Rψ(1). -/
theorem left_support_of_corner {P a : S} (hP : P * P = P) (ha : P * a * P = a) :
    P * a = a := by
  calc
    P * a = P * (P * a * P) := by rw [ha]
    _ = P * a * P := by simp only [← mul_assoc, hP]
    _ = a := ha

theorem right_support_of_corner {P a : S} (hP : P * P = P) (ha : P * a * P = a) :
    a * P = a := by
  calc
    a * P = (P * a * P) * P := by rw [ha]
    _ = a := by rw [mul_assoc, hP, ha]

/-- **the Steinberg kernel argument, Theorem kernel.** A nonunital coefficient map with a commuting
binary splitting pair annihilates the entire rank-six matrix kernel in one step.
The four support equations say exactly that U₀,U₁,V₀,V₁ lie in PRP, P=ψ(1). -/
theorem kernel_annihilation (ψ : R →ₙ+* R) (U₀ U₁ V₀ V₁ : R)
    (hU₀ : ψ 1 * U₀ * ψ 1 = U₀) (hU₁ : ψ 1 * U₁ * ψ 1 = U₁)
    (hV₀ : ψ 1 * V₀ * ψ 1 = V₀) (hV₁ : ψ 1 * V₁ * ψ 1 = V₁)
    (cU₀ : ∀ a, Commute U₀ (ψ a)) (cU₁ : ∀ a, Commute U₁ (ψ a))
    (cV₀ : ∀ a, Commute V₀ (ψ a)) (cV₁ : ∀ a, Commute V₁ (ψ a))
    (h00 : V₀ * U₀ = ψ 1) (h11 : V₁ * U₁ = ψ 1)
    (h01 : V₀ * U₁ = 0) (h10 : V₁ * U₀ = 0)
    (hsum : U₀ * V₀ + U₁ * V₁ = ψ 1)
    (z : Group (Fin 6) R) (hz : matrixMap z = 1) : coefficientMap ψ z = 1 := by
  have hP : ψ 1 * ψ 1 = ψ 1 := by rw [← map_mul, one_mul]
  let p : SupportedPair ψ := {
    U := U₀, V := V₀, VU := h00
    PU := left_support_of_corner hP hU₀
    UP := right_support_of_corner hP hU₀
    PV := left_support_of_corner hP hV₀
    VP := right_support_of_corner hP hV₀
    commU := cU₀, commV := cV₀ }
  let q : SupportedPair ψ := {
    U := U₁, V := V₁, VU := h11
    PU := left_support_of_corner hP hU₁
    UP := right_support_of_corner hP hU₁
    PV := left_support_of_corner hP hV₁
    VP := right_support_of_corner hP hV₁
    commU := cU₁, commV := cV₁ }
  exact p.annihilation q h01 h10 hsum hz

end Steinberg

end FiniteAlgebraicEnvelopes

end OAI

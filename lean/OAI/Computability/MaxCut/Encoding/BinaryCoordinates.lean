import Mathlib
import OAI.Computability.MaxCut.Model

namespace OAI

/-!
Dimension-independent transport between the compact bit-vector coordinates of
the finite motif and the coordinate functions used by the later constructions.
The vector-space addition involved here is XOR, not modular integer addition.
-/
namespace MaxCutGames.Integration.BinaryCoordinates

abbrev Coordinates (n : Nat) := Fin n → Bool

def pack : {n : Nat} → Coordinates n → BitVec n
  | 0, _ => 0
  | _ + 1, f => BitVec.concat (pack (fun i => f i.succ)) (f 0)

def unpack {n : Nat} (v : BitVec n) : Coordinates n :=
  fun i => v.getLsbD i.val

theorem pack_get {n : Nat} (f : Coordinates n) (i : Fin n) :
    (pack f).getLsbD i.val = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact BitVec.getLsbD_concat_zero
    · exact (BitVec.getLsbD_concat_succ).trans (ih (fun j => f j.succ) j)

theorem unpack_pack {n : Nat} (f : Coordinates n) : unpack (pack f) = f := by
  funext i
  exact pack_get f i

theorem pack_unpack {n : Nat} (v : BitVec n) : pack (unpack v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact pack_get (unpack v) ⟨i, hi⟩

theorem unpack_injective {n : Nat} : Function.Injective (@unpack n) := by
  intro u v h
  have h' := congrArg pack h
  simpa only [pack_unpack] using h'

theorem pack_injective {n : Nat} : Function.Injective (@pack n) := by
  intro u v h
  have h' := congrArg unpack h
  simpa only [unpack_pack] using h'

theorem unpack_xor {n : Nat} (u v : BitVec n) :
    unpack (u ^^^ v) = fun i => (unpack u i ^^ unpack v i) := by
  funext i
  exact BitVec.getLsbD_xor

theorem pack_xor {n : Nat} (u v : Coordinates n) :
    pack (fun i => (u i ^^ v i)) = pack u ^^^ pack v := by
  apply unpack_injective
  rw [unpack_pack, unpack_xor, unpack_pack, unpack_pack]

theorem unpack_zero {n : Nat} : unpack (0 : BitVec n) = fun _ => false := by
  funext i
  simp [unpack]

theorem pack_zero {n : Nat} : pack (fun _ : Fin n => false) = 0 := by
  apply unpack_injective
  rw [unpack_pack, unpack_zero]

end MaxCutGames.Integration.BinaryCoordinates

/-! Exact transport from XOR bit vectors to vector spaces over `ZMod 2`. -/
namespace MaxCutGames.Integration.BinaryLinear

open BinaryCoordinates

abbrev F2 := ZMod 2
abbrev Vector (n : Nat) := Fin n → F2

def ofBit (b : Bool) : F2 := if b then 1 else 0
def toBit (a : F2) : Bool := decide (a = 1)

theorem scalar_cases : ∀ a : F2, a = 0 ∨ a = 1 := by decide
theorem ofBit_toBit : ∀ a : F2, ofBit (toBit a) = a := by decide
theorem toBit_ofBit : ∀ b : Bool, toBit (ofBit b) = b := by decide
theorem ofBit_xor : ∀ a b : Bool, ofBit (a ^^ b) = ofBit a + ofBit b := by decide
theorem toBit_add : ∀ a b : F2, toBit (a + b) = (toBit a ^^ toBit b) := by decide

def toVector {n : Nat} (v : BitVec n) : Vector n := fun i => ofBit (unpack v i)
def fromVector {n : Nat} (v : Vector n) : BitVec n := pack (fun i => toBit (v i))

theorem toVector_fromVector {n : Nat} (v : Vector n) : toVector (fromVector v) = v := by
  funext i
  simp only [toVector, fromVector, unpack_pack, ofBit_toBit]

theorem fromVector_toVector {n : Nat} (v : BitVec n) : fromVector (toVector v) = v := by
  simp only [fromVector, toVector, toBit_ofBit]
  exact pack_unpack v

def coordinatesEquiv (n : Nat) : BitVec n ≃ Vector n where
  toFun := toVector
  invFun := fromVector
  left_inv := fromVector_toVector
  right_inv := toVector_fromVector

theorem toVector_xor {n : Nat} (u v : BitVec n) :
    toVector (u ^^^ v) = toVector u + toVector v := by
  funext i
  simp only [toVector, unpack_xor, ofBit_xor, Pi.add_apply]

theorem fromVector_add {n : Nat} (u v : Vector n) :
    fromVector (u + v) = fromVector u ^^^ fromVector v := by
  simp only [fromVector, Pi.add_apply, toBit_add, pack_xor]

@[simp] theorem toVector_zero {n : Nat} : toVector (0 : BitVec n) = 0 := by
  unfold toVector
  rw [unpack_zero]
  rfl

@[simp] theorem fromVector_zero {n : Nat} : fromVector (0 : Vector n) = 0 := by
  simp [fromVector, toBit, pack_zero]

/-- A zero-preserving XOR-additive map becomes a genuine binary linear map. -/
def liftLinear {n m : Nat} (f : BitVec n → BitVec m)
    (hzero : f 0 = 0) (hadd : ∀ x y, f (x ^^^ y) = f x ^^^ f y) :
    Vector n →ₗ[F2] Vector m where
  toFun x := toVector (f (fromVector x))
  map_add' x y := by rw [fromVector_add, hadd, toVector_xor]
  map_smul' c x := by
    rcases scalar_cases c with rfl | rfl
    · change toVector (f (fromVector (0 • x))) = 0 • toVector (f (fromVector x))
      rw [zero_smul, fromVector_zero, hzero, toVector_zero, zero_smul]
    · simp

theorem liftLinear_apply {n m : Nat} (f : BitVec n → BitVec m)
    (hzero : f 0 = 0) (hadd : ∀ x y, f (x ^^^ y) = f x ^^^ f y)
    (x : Vector n) :
    liftLinear f hzero hadd x = toVector (f (fromVector x)) := rfl

theorem finrank_vector (n : Nat) : Module.finrank F2 (Vector n) = n := by
  simp [Vector]

end MaxCutGames.Integration.BinaryLinear

end OAI

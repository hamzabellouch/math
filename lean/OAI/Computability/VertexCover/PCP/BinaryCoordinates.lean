import Mathlib

namespace OAI

                                                                                      

namespace UniqueGames.Integration.BinaryCoordinates

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

end UniqueGames.Integration.BinaryCoordinates

end OAI

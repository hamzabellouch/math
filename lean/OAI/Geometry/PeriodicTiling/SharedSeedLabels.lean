import OAI.Geometry.PeriodicTiling.SharedSeedRegions
import OAI.Geometry.PeriodicTiling.TilingBasic

namespace OAI

universe uS uK

noncomputable section

namespace PeriodicTilingThree.SharedSeed

def ActiveOne {m : ℕ} : LabelledResidue m → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

def ActiveTwo {m : ℕ} : LabelledResidue m → Prop
  | Sum.inl _ => False
  | Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inr _) => False

def firstLabel {m : ℕ} : LabelledResidue m → ZMod 2
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl v) => v.2
  | Sum.inr (Sum.inr v) => v.2.1

def secondLabel {m : ℕ} : LabelledResidue m → ZMod 3
  | Sum.inl y => y
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr v) => v.2.2

def rotateMap {m : ℕ} (t : ℤ) : LabelledResidue m → LabelledResidue m
  | Sum.inl y => Sum.inl (y + (t : ZMod 3))
  | Sum.inr (Sum.inl (c, y)) => Sum.inr (Sum.inl (c, y + (t : ZMod 2)))
  | Sum.inr (Sum.inr (c, y, z)) =>
      Sum.inr (Sum.inr (c, y + (t : ZMod 2), z + (t : ZMod 3)))

@[simp] theorem rotateMap_zero {m : ℕ} (s : LabelledResidue m) :
    rotateMap 0 s = s := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩) <;> simp [rotateMap]

theorem rotateMap_add {m : ℕ} (t u : ℤ) (s : LabelledResidue m) :
    rotateMap (t + u) s = rotateMap t (rotateMap u s) := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩) <;>
    simp [rotateMap, Int.cast_add, add_comm, add_left_comm]

def rotate {m : ℕ} (t : ℤ) : Equiv.Perm (LabelledResidue m) where
  toFun := rotateMap t
  invFun := rotateMap (-t)
  left_inv s := by rw [← rotateMap_add, neg_add_cancel, rotateMap_zero]
  right_inv s := by rw [← rotateMap_add, add_neg_cancel, rotateMap_zero]

@[simp] theorem rotate_apply {m : ℕ} (t : ℤ) (s : LabelledResidue m) :
    rotate t s = rotateMap t s := rfl

@[simp] theorem rotate_zero {m : ℕ} (s : LabelledResidue m) : rotate 0 s = s :=
  rotateMap_zero s

theorem rotate_add {m : ℕ} (t u : ℤ) (s : LabelledResidue m) :
    rotate (t + u) s = rotate t (rotate u s) := rotateMap_add t u s

@[simp] theorem activeOne_rotate {m : ℕ} (t : ℤ) (s : LabelledResidue m) :
    ActiveOne (rotate t s) ↔ ActiveOne s := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩) <;> rfl

@[simp] theorem activeTwo_rotate {m : ℕ} (t : ℤ) (s : LabelledResidue m) :
    ActiveTwo (rotate t s) ↔ ActiveTwo s := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩) <;> rfl

theorem firstLabel_rotate {m : ℕ} (t : ℤ) (s : LabelledResidue m)
    (hs : ¬ ActiveOne s) : firstLabel (rotate t s) = firstLabel s + (t : ZMod 2) := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · exact False.elim (hs trivial)
  · rfl
  · rfl

theorem secondLabel_rotate {m : ℕ} (t : ℤ) (s : LabelledResidue m)
    (hs : ¬ ActiveTwo s) : secondLabel (rotate t s) = secondLabel s + (t : ZMod 3) := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · rfl
  · exact False.elim (hs trivial)
  · rfl

theorem rotate_fixed_on_activeOne {m : ℕ} {t : ℤ} {s : LabelledResidue m}
    (hs : ActiveOne s) (ht : (t : ZMod 3) = 0) : rotate t s = s := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · simp [rotate, rotateMap, ht]
  · exact False.elim hs
  · exact False.elim hs

theorem rotate_fixed_on_activeTwo {m : ℕ} {t : ℤ} {s : LabelledResidue m}
    (hs : ActiveTwo s) (ht : (t : ZMod 2) = 0) : rotate t s = s := by
  rcases s with y | (⟨c, y⟩ | ⟨c, y, z⟩)
  · exact False.elim hs
  · simp [rotate, rotateMap, ht]
  · exact False.elim hs

def rotation {S : Type uS} {m : ℕ} (e : S ≃ LabelledResidue m) (t : ℤ) : Equiv.Perm S :=
  (e.trans (rotate t)).trans e.symm

@[simp] theorem rotation_apply {S : Type uS} {m : ℕ}
    (e : S ≃ LabelledResidue m) (t : ℤ) (s : S) :
    rotation e t s = e.symm (rotate t (e s)) := rfl

@[simp] theorem label_rotation {S : Type uS} {m : ℕ}
    (e : S ≃ LabelledResidue m) (t : ℤ) (s : S) :
    e (rotation e t s) = rotate t (e s) := e.apply_symm_apply _

theorem rotation_add {S : Type uS} {m : ℕ}
    (e : S ≃ LabelledResidue m) (t u : ℤ) (s : S) :
    rotation e (t + u) s = rotation e t (rotation e u s) := by
  simp only [rotation_apply, Equiv.apply_symm_apply, rotate_add]

def sharedOutput {S : Type uS} {m D : ℕ}
    (e : S ≃ LabelledResidue m) (code : S ≃ ZMod D) (t : ℤ) (s : S) : ZMod D :=
  code (rotation e t s)

@[simp] theorem decode_sharedOutput {S : Type uS} {m D : ℕ}
    (e : S ≃ LabelledResidue m) (code : S ≃ ZMod D) (t : ℤ) (s : S) :
    e (code.symm (sharedOutput e code t s)) = rotate t (e s) := by
  simp only [sharedOutput, Equiv.symm_apply_apply, label_rotation]

def sharedZ {p m : ℕ} {K : Type uK}
    (e : Residues p ≃ LabelledResidue m) (code : Residues p ≃ ZMod (p ^ 4))
    (x : Plane) (_k : K) : ZMod (p ^ 4) :=
  sharedOutput e code x.1 ((x.1 : ZMod (p ^ 2)), (x.2 : ZMod (p ^ 2)))

def commonZ {p : ℕ} {K : Type uK} (hp : p.Prime) (hlarge : 200 < p)
    (x : Plane) (_k : K) : ZMod (p ^ 4) :=
  sharedOutput (residueEquiv hp hlarge) (outputEquiv hlarge) x.1 (residue p x)

end PeriodicTilingThree.SharedSeed

end

end OAI

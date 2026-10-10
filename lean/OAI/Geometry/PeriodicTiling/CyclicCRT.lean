import OAI.Geometry.PeriodicTiling.EncodingParameters
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Basic

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open scoped BigOperators

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

def digitEquivRing (i : Channel p) :
    ZMod (E.r i) ≃+* (∀ j : Label p i, ZMod (E.digitPrime i j)) :=
  ZMod.prodEquivPi (E.digitPrime i) (E.digitPrime_pairwise i)

def digitEquiv (i : Channel p) :
    ZMod (E.r i) ≃+ (∀ j : Label p i, ZMod (E.digitPrime i j)) :=
  (digitEquivRing E i).toAddEquiv

theorem digitPrime_dvd_r (i : Channel p) (j : Label p i) :
    E.digitPrime i j ∣ E.r i :=
  Finset.dvd_prod_of_mem (E.digitPrime i) (Finset.mem_univ j)

@[simp] theorem digitEquiv_intCast (i : Channel p) (z : ℤ) (j : Label p i) :
    digitEquiv E i (z : ZMod (E.r i)) j = (z : ZMod (E.digitPrime i j)) := by
  exact congrArg (fun f : ∀ j : Label p i, ZMod (E.digitPrime i j) => f j)
    (map_intCast (digitEquivRing E i) z)

theorem digitEquiv_apply (i : Channel p) (x : ZMod (E.r i)) (j : Label p i) :
    digitEquiv E i x j = (ZMod.cast x : ZMod (E.digitPrime i j)) := by
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  rw [digitEquiv_intCast, ZMod.cast_intCast (digitPrime_dvd_r E i j)]

def digitSubgroup (i : Channel p) (j : Label p i) : AddSubgroup (ZMod (E.r i)) where
  carrier := {x | ∀ k : Label p i, k ≠ j → digitEquiv E i x k = 0}
  zero_mem' := by
    intro k _hk
    simp
  add_mem' := by
    intro x y hx hy k hk
    simp [map_add, hx k hk, hy k hk]
  neg_mem' := by
    intro x hx k hk
    simp [map_neg, hx k hk]

@[simp] theorem mem_digitSubgroup (i : Channel p) (j : Label p i) (x : ZMod (E.r i)) :
    x ∈ digitSubgroup E i j ↔
      ∀ k : Label p i, k ≠ j → digitEquiv E i x k = 0 := Iff.rfl

theorem sub_mem_digitSubgroup_iff (i : Channel p) (j : Label p i)
    (x y : ZMod (E.r i)) :
    x - y ∈ digitSubgroup E i j ↔
      ∀ k : Label p i, k ≠ j → digitEquiv E i x k = digitEquiv E i y k := by
  simp [mem_digitSubgroup, map_sub, sub_eq_zero]

def digitSingle (i : Channel p) (j : Label p i) (x : ZMod (E.digitPrime i j)) :
    ZMod (E.r i) :=
  (digitEquiv E i).symm (Pi.single j x)

@[simp] theorem digitEquiv_digitSingle (i : Channel p) (j : Label p i)
    (x : ZMod (E.digitPrime i j)) :
    digitEquiv E i (digitSingle E i j x) = Pi.single j x :=
  (digitEquiv E i).apply_symm_apply _

theorem digitSingle_mem (i : Channel p) (j : Label p i)
    (x : ZMod (E.digitPrime i j)) : digitSingle E i j x ∈ digitSubgroup E i j := by
  intro k hk
  rw [digitEquiv_digitSingle]
  exact Pi.single_eq_of_ne (M := fun j : Label p i => ZMod (E.digitPrime i j)) hk x

end PeriodicTilingThree

end

end OAI

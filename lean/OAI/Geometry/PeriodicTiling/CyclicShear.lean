import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI

namespace PeriodicTilingThree.CyclicShear

noncomputable section

def low (r : ℕ) : ZMod (r ^ 2) →+ ZMod r :=
  (ZMod.castHom (dvd_pow_self r (by decide : 2 ≠ 0)) (ZMod r)).toAddMonoidHom

@[simp] theorem low_natCast (r m : ℕ) : low r (m : ZMod (r ^ 2)) = (m : ZMod r) := by
  simp [low]

@[simp] theorem low_intCast (r : ℕ) (m : ℤ) :
    low r (m : ZMod (r ^ 2)) = (m : ZMod r) := by
  simp [low]

private def highInteger (r : ℕ) : ℤ →+ ZMod (r ^ 2) where
  toFun z := (r : ZMod (r ^ 2)) * (z : ZMod (r ^ 2))
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

private theorem highInteger_modulus (r : ℕ) : highInteger r r = 0 := by
  dsimp only [highInteger]
  change (r : ZMod (r ^ 2)) * ((r : ℤ) : ZMod (r ^ 2)) = 0
  rw [Int.cast_natCast, ← pow_two, ← Nat.cast_pow]
  exact ZMod.natCast_self (r ^ 2)

def highMul (r : ℕ) : ZMod r →+ ZMod (r ^ 2) :=
  ZMod.lift r ⟨highInteger r, highInteger_modulus r⟩

@[simp] theorem highMul_intCast (r : ℕ) (m : ℤ) :
    highMul r (m : ZMod r) = (r : ZMod (r ^ 2)) * (m : ZMod (r ^ 2)) := by
  exact ZMod.lift_coe r ⟨highInteger r, highInteger_modulus r⟩ m

@[simp] theorem highMul_natCast (r m : ℕ) :
    highMul r (m : ZMod r) = (r : ZMod (r ^ 2)) * (m : ZMod (r ^ 2)) := by
  simpa using highMul_intCast r (m : ℤ)

theorem highMul_apply (r : ℕ) [NeZero r] (b : ZMod r) :
    highMul r b = (r : ZMod (r ^ 2)) * (b.val : ZMod (r ^ 2)) := by
  simpa using highMul_natCast r b.val

theorem highMul_val (r : ℕ) [NeZero r] (b : ZMod r) :
    (highMul r b).val = r * b.val := by
  rw [highMul_apply, ← Nat.cast_mul]
  apply ZMod.val_natCast_of_lt
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  simpa [pow_two] using Nat.mul_lt_mul_of_pos_left (ZMod.val_lt b) hr

theorem highMul_injective (r : ℕ) [NeZero r] : Function.Injective (highMul r) := by
  intro b c h
  have hv := congrArg ZMod.val h
  rw [highMul_val, highMul_val] at hv
  have hv' : b.val = c.val := Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (NeZero.ne r)) hv
  exact ZMod.val_injective r hv'

@[simp] theorem low_highMul (r : ℕ) (b : ZMod r) : low r (highMul r b) = 0 := by
  obtain ⟨m, rfl⟩ := ZMod.intCast_surjective b
  rw [highMul_intCast]
  change (ZMod.castHom (dvd_pow_self r (by decide : 2 ≠ 0)) (ZMod r))
    ((r : ZMod (r ^ 2)) * (m : ZMod (r ^ 2))) = 0
  simp only [map_mul, map_natCast, map_intCast, ZMod.natCast_self, zero_mul]

theorem mem_range_highMul_iff (r : ℕ) [NeZero r] (v : ZMod (r ^ 2)) :
    v ∈ Set.range (highMul r) ↔ low r v = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact low_highMul r b
  · intro h
    have hcast : (v.val : ZMod r) = 0 := by
      have hv := congrArg (low r) (ZMod.natCast_zmod_val v)
      simpa only [low_natCast, h] using hv
    obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff v.val r).mp hcast
    refine ⟨(m : ZMod r), ?_⟩
    rw [highMul_natCast, ← Nat.cast_mul, ← hm]
    exact ZMod.natCast_zmod_val v

theorem range_highMul (r : ℕ) [NeZero r] :
    Set.range (highMul r) = ((low r).ker : Set (ZMod (r ^ 2))) := by
  ext v
  exact mem_range_highMul_iff r v

def highEquiv (r : ℕ) [NeZero r] : ZMod r ≃ (low r).ker :=
  Equiv.ofBijective (fun b => ⟨highMul r b, low_highMul r b⟩)
    ⟨fun _ _ h => highMul_injective r (congrArg Subtype.val h), by
      intro v
      obtain ⟨b, hb⟩ := (mem_range_highMul_iff r v).mpr v.property
      exact ⟨b, Subtype.ext hb⟩⟩

@[simp] theorem highEquiv_apply (r : ℕ) [NeZero r] (b : ZMod r) :
    (highEquiv r b : ZMod (r ^ 2)) = highMul r b := rfl

def shear (r : ℕ) (x : ℤ) (k b : ZMod r) : ZMod (r ^ 2) :=
  (x : ZMod (r ^ 2)) + ((k - (x : ZMod r)).val : ZMod (r ^ 2)) + highMul r b

@[simp] theorem low_shear (r : ℕ) [NeZero r] (x : ℤ) (k b : ZMod r) :
    low r (shear r x k b) = k := by
  simp only [shear, map_add, low_intCast, low_natCast, low_highMul, add_zero,
    ZMod.natCast_zmod_val]
  abel

theorem shear_injective (r : ℕ) [NeZero r] (x : ℤ) (k : ZMod r) :
    Function.Injective (shear r x k) := by
  intro b c h
  apply highMul_injective r
  exact add_left_cancel h

theorem shear_eq_zero_add (r : ℕ) (x : ℤ) (k b : ZMod r) :
    shear r x k b = shear r x k 0 + highMul r b := by
  simp [shear]

theorem shear_surjective_fiber (r : ℕ) [NeZero r] (x : ℤ) (k : ZMod r) :
    Function.Surjective (fun b : ZMod r =>
      (⟨shear r x k b, low_shear r x k b⟩ : {v : ZMod (r ^ 2) // low r v = k})) := by
  intro v
  have hz : low r (v.val - shear r x k 0) = 0 := by
    rw [map_sub, v.property, low_shear, sub_self]
  obtain ⟨b, hb⟩ := (mem_range_highMul_iff r _).mpr hz
  refine ⟨b, Subtype.ext ?_⟩
  change shear r x k b = v.val
  rw [shear_eq_zero_add, hb]
  abel

def shearEquiv (r : ℕ) [NeZero r] (x : ℤ) (k : ZMod r) :
    ZMod r ≃ {v : ZMod (r ^ 2) // low r v = k} :=
  Equiv.ofBijective (fun b => ⟨shear r x k b, low_shear r x k b⟩)
    ⟨fun _ _ h => shear_injective r x k (congrArg Subtype.val h),
      shear_surjective_fiber r x k⟩

@[simp] theorem shearEquiv_apply (r : ℕ) [NeZero r] (x : ℤ) (k b : ZMod r) :
    (shearEquiv r x k b : ZMod (r ^ 2)) = shear r x k b := rfl

theorem shear_add (r : ℕ) (x h : ℤ) (k b : ZMod r) :
    shear r (x + h) (k + (h : ZMod r)) b = shear r x k b + (h : ZMod (r ^ 2)) := by
  simp only [shear, Int.cast_add]
  abel_nf

theorem shear_source_add (r : ℕ) (x h : ℤ) (k l b : ZMod r)
    (hl : (h : ZMod r) = l) :
    shear r (x - h) (k - l) b + (h : ZMod (r ^ 2)) = shear r x k b := by
  simpa [hl] using (shear_add r (x - h) h (k - l) b).symm

end

end PeriodicTilingThree.CyclicShear

end OAI

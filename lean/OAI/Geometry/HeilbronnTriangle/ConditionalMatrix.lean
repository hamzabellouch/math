import OAI.Geometry.HeilbronnTriangle.ConditionalDigits
import OAI.Geometry.HeilbronnTriangle.RankOneMinors
import OAI.Geometry.HeilbronnTriangle.DigitUnits

namespace OAI


namespace Problem355.ConditionalMatrix

open scoped BigOperators

abbrev Header (X : Type*) (k : ℕ) :=
  (Fin 3 → Fin k → X) × (Fin 2 → Fin k → X)

abbrev Draw (X : Type*) (k : ℕ) :=
  Header X k × ((Fin 2 × Fin 2) → Fin k → X)

def picked {X : Type*} {k : ℕ} (z : Draw X k) (a c : Fin 3) (v : Fin k) : X :=
  Fin.cases (z.1.1 c v)
    (fun i => Fin.cases (z.1.2 i v) (fun l => z.2 (i, l) v) c) a

def drawEquiv {X : Type*} {k : ℕ} : Draw X k ≃ (Fin 3 → Fin 3 → Fin k → X) where
  toFun z := picked z
  invFun f := ((fun c v => f 0 c v, fun i v => f i.succ 0 v),
    fun i v => f i.1.succ i.2.succ v)
  left_inv z := by
    apply Prod.ext
    · apply Prod.ext <;> rfl
    · funext i v
      rfl
  right_inv f := by
    funext a c v
    refine Fin.cases ?_ (fun i => ?_) a
    · rfl
    · refine Fin.cases ?_ (fun l => ?_) c <;> rfl

def entryValue {X : Type*} {B k : ℕ}
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (z : Draw X k) (a c : Fin 3) : ℕ :=
  ∑ v : Fin k, (digit a c v (picked z a c v)).val * B ^ v.val

def residueMatrix {X : Type*} {B k : ℕ}
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (z : Draw X k) (j : ℕ) : Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)) :=
  fun a c => (entryValue digit z a c : ZMod (B ^ j))

def arrayMatrix {X : Type*} {B k : ℕ}
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (f : Fin 3 → Fin 3 → Fin k → X) (j : ℕ) :
    Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)) :=
  fun a c => ((∑ v : Fin k, (digit a c v (f a c v)).val * B ^ v.val : ℕ) : ZMod (B ^ j))

lemma residueMatrix_eq_arrayMatrix {X : Type*} {B k : ℕ}
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B) (z : Draw X k) (j : ℕ) :
    residueMatrix digit z j = arrayMatrix digit (drawEquiv z) j := rfl

theorem encoded_isUnit {B k j : ℕ} (hB : B.Prime) (hk : 0 < k) (hj : 0 < j)
    (d : Fin k → Fin B) (hpos : ∀ v, 0 < (d v).val) :
    IsUnit (((∑ v : Fin k, (d v).val * B ^ v.val : ℕ)) : ZMod (B ^ j)) := by
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hB hj).mpr
  intro hdiv
  have hm := Nat.mod_eq_zero_of_dvd hdiv
  cases k with
  | zero => omega
  | succ k =>
    rw [← Digits.ofDigits_ofFn_eq_sum, Nat.ofDigits_mod_eq_head!, List.ofFn_succ] at hm
    have heq : (d 0).val % B = 0 := by simpa using hm
    rw [Nat.mod_eq_of_lt (d 0).isLt] at heq
    exact (Nat.ne_of_gt (hpos 0)) heq

theorem moment_le_two {X : Type*} [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hinj : ∀ a c v, Function.Injective (digit a c v))
    (hpos : ∀ a c v x, 0 < (digit a c v x).val)
    (b : Draw X k → ℕ) (hb : ∀ z, b z ≤ k)
    (hminor : ∀ j, 1 ≤ j → j ≤ k → ∀ z, j ≤ b z →
      UnitPivot.MinorsVanish (residueMatrix digit z j))
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ z : Draw X k, (1 / (Fintype.card (Draw X k) : ℝ)) * (B : ℝ) ^ b z) ≤ 2 := by
  classical
  apply ConditionalDigits.conditional_divisor_moment_le_two hB.one_lt
    (fun i v x => digit i.1.succ i.2.succ v x)
    (fun i v => hinj i.1.succ i.2.succ v) b hb
  · intro j hjpos hj
    let row : Header X k → Fin 3 → ℕ :=
      fun a c => ∑ v : Fin k, (digit 0 c v (a.1 c v)).val * B ^ v.val
    let col : Header X k → Fin 2 → ℕ :=
      fun a i => ∑ v : Fin k, (digit i.succ 0 v (a.2 i v)).val * B ^ v.val
    have hunit (a : Header X k) : IsUnit ((row a 0 : ℕ) : ZMod (B ^ j)) :=
      encoded_isUnit hB hk hjpos (fun v => digit 0 0 v (a.1 0 v))
        (fun v => hpos 0 0 v (a.1 0 v))
    let pivot : Header X k → (ZMod (B ^ j))ˣ := fun a => (hunit a).unit
    refine ⟨pivot, fun a i =>
      (col a i.1 : ZMod (B ^ j)) * (row a i.2.succ : ZMod (B ^ j)), ?_⟩
    intro z hz i
    have hpivot : (pivot z.1 : ZMod (B ^ j)) = (row z.1 0 : ZMod (B ^ j)) :=
      (hunit z.1).unit_spec
    rw [hpivot]
    have h := hminor j hjpos hj z hz 0 i.1.succ 0 i.2.succ
    change (row z.1 0 : ZMod (B ^ j)) *
        ((∑ v : Fin k, (digit i.1.succ i.2.succ v (z.2 i v)).val * B ^ v.val : ℕ) : ZMod (B ^ j)) =
      (row z.1 i.2.succ : ZMod (B ^ j)) * (col z.1 i.1 : ZMod (B ^ j)) at h
    exact h.trans (mul_comm _ _)
  · simpa using hsmall

theorem array_moment_le_two {X : Type*} [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hinj : ∀ a c v, Function.Injective (digit a c v))
    (hpos : ∀ a c v x, 0 < (digit a c v x).val)
    (b : (Fin 3 → Fin 3 → Fin k → X) → ℕ) (hb : ∀ f, b f ≤ k)
    (hminor : ∀ j, 1 ≤ j → j ≤ k → ∀ f, j ≤ b f →
      UnitPivot.MinorsVanish (arrayMatrix digit f j))
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ f : Fin 3 → Fin 3 → Fin k → X,
      (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) * (B : ℝ) ^ b f) ≤ 2 := by
  have h := moment_le_two hB hk digit hinj hpos (fun z => b (drawEquiv z))
    (fun z => hb (drawEquiv z))
    (fun j hj hk z hz => hminor j hj hk (drawEquiv z) hz) hsmall
  have hcard := Fintype.card_congr (drawEquiv (X := X) (k := k))
  rw [hcard] at h
  have hsum := (drawEquiv (X := X) (k := k)).sum_comp
    (fun f => (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) * (B : ℝ) ^ b f)
  rw [← hsum]
  exact h

noncomputable def prescribedDigit {r m B k : ℕ} [NeZero r] (hbound : r * m < B)
    (residue : Fin 3 → Fin 3 → Fin k → ZMod r)
    (a c : Fin 3) (v : Fin k) (x : Fin m) : Fin B :=
  ⟨(DigitUnits.digitFiberEquiv (residue a c v) m x).val,
    lt_of_le_of_lt (DigitUnits.digitFiberEquiv_bounds (residue a c v) m x).2.1 hbound⟩

lemma prescribedDigit_injective {r m B k : ℕ} [NeZero r] (hbound : r * m < B)
    (residue : Fin 3 → Fin 3 → Fin k → ZMod r) (a c : Fin 3) (v : Fin k) :
    Function.Injective (prescribedDigit hbound residue a c v) := by
  intro x y hxy
  apply (DigitUnits.digitFiberEquiv (residue a c v) m).injective
  apply Subtype.ext
  exact congrArg Fin.val hxy

lemma prescribedDigit_positive {r m B k : ℕ} [NeZero r] (hbound : r * m < B)
    (residue : Fin 3 → Fin 3 → Fin k → ZMod r) (a c : Fin 3) (v : Fin k) (x : Fin m) :
    0 < (prescribedDigit hbound residue a c v x).val :=
  (DigitUnits.digitFiberEquiv_bounds (residue a c v) m x).1

lemma prescribedDigit_residue {r m B k : ℕ} [NeZero r] (hbound : r * m < B)
    (residue : Fin 3 → Fin 3 → Fin k → ZMod r) (a c : Fin 3) (v : Fin k) (x : Fin m) :
    ((prescribedDigit hbound residue a c v x).val : ZMod r) = residue a c v :=
  (DigitUnits.digitFiberEquiv_bounds (residue a c v) m x).2.2

theorem prescribed_moment_le_two {r m B k : ℕ} [NeZero r] [NeZero m]
    (hB : B.Prime) (hk : 0 < k) (hbound : r * m < B)
    (residue : Fin 3 → Fin 3 → Fin k → ZMod r)
    (b : Draw (Fin m) k → ℕ) (hb : ∀ z, b z ≤ k)
    (hminor : ∀ j, 1 ≤ j → j ≤ k → ∀ z, j ≤ b z →
      UnitPivot.MinorsVanish (residueMatrix (prescribedDigit hbound residue) z j))
    (hsmall : (B : ℝ) * (1 / (m : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ z : Draw (Fin m) k, (1 / (Fintype.card (Draw (Fin m) k) : ℝ)) *
      (B : ℝ) ^ b z) ≤ 2 := by
  exact moment_le_two hB hk (prescribedDigit hbound residue)
    (prescribedDigit_injective hbound residue) (prescribedDigit_positive hbound residue)
    b hb hminor (by simpa using hsmall)

end Problem355.ConditionalMatrix

end OAI

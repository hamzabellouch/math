import OAI.Geometry.PeriodicTiling.TilingBasic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace PeriodicTilingThree

abbrev Residue3 (m : ℕ) := Fin 3 → ZMod m
abbrev LiftAlphabet := Fin 3 → Fin 5
abbrev LiftAssignment (m : ℕ) := Residue3 m → LiftAlphabet

def residueMod (m : ℕ) (d : Lattice 3) : Residue3 m := fun i => (d i : ZMod m)

def can {m : ℕ} (v : Residue3 m) : Lattice 3 := fun i => ((v i).val : ℤ)

def signed (h : LiftAlphabet) : Lattice 3 := fun i => (h i).val - (2 : ℤ)

def representative (m : ℕ) [NeZero m] (ω : LiftAssignment m)
    (v : Residue3 m) : Lattice 3 :=
  fun i => can v i + (m : ℤ) * signed (ω v) i

@[simp] theorem residueMod_can {m : ℕ} [NeZero m] (v : Residue3 m) :
    residueMod m (can v) = v := by
  funext i
  simp [residueMod, can]

@[simp] theorem representative_residue (m : ℕ) [NeZero m]
    (ω : LiftAssignment m) (v : Residue3 m) :
    residueMod m (representative m ω v) = v := by
  funext i
  simp [residueMod, representative, can]

theorem representative_injective (m : ℕ) [NeZero m] (ω : LiftAssignment m) :
    Function.Injective (representative m ω) := by
  intro u v huv
  have h := congrArg (residueMod m) huv
  simpa only [representative_residue] using h

theorem can_nonneg {m : ℕ} (v : Residue3 m) (i : Fin 3) : 0 ≤ can v i := by
  dsimp only [can]
  exact_mod_cast (Nat.zero_le (v i).val)

theorem can_lt {m : ℕ} [NeZero m] (v : Residue3 m) (i : Fin 3) :
    can v i < (m : ℤ) := by
  dsimp only [can]
  exact_mod_cast (v i).val_lt

theorem signed_bounds (h : LiftAlphabet) (i : Fin 3) :
    -2 ≤ signed h i ∧ signed h i ≤ 2 := by
  have hi := (h i).isLt
  dsimp [signed]
  omega

def Requested (m : ℕ) (d : Lattice 3) : Prop :=
  (∀ i, |d i| ≤ (m : ℤ)) ∧ ¬ ∀ i, (m : ℤ) ∣ d i

noncomputable def requestedVectors (m : ℕ) : Finset (Lattice 3) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(m : ℤ)) (m : ℤ))).filter
    (fun d => ¬ ∀ i, (m : ℤ) ∣ d i)

@[simp] theorem mem_requestedVectors {m : ℕ} {d : Lattice 3} :
    d ∈ requestedVectors m ↔ Requested m d := by
  classical
  simp only [requestedVectors, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_Icc, Requested, abs_le]

theorem card_requestedVectors_le (m : ℕ) :
    (requestedVectors m).card ≤ (2 * m + 1) ^ 3 := by
  classical
  have hc : (Finset.Icc (-(m : ℤ)) (m : ℤ)).card = 2 * m + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    (requestedVectors m).card ≤
        (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(m : ℤ)) (m : ℤ))).card :=
      Finset.card_filter_le _ _
    _ = (2 * m + 1) ^ 3 := by rw [Fintype.card_piFinset_const, hc]

theorem requested_residueMod_ne_zero {m : ℕ} {d : Lattice 3}
    (hd : Requested m d) : residueMod m d ≠ 0 := by
  intro h
  apply hd.2
  intro i
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (d i) m).mp
  exact congrFun h i

theorem requested_successor_ne {m : ℕ} {d : Lattice 3}
    (hd : Requested m d) (u : Residue3 m) : u + residueMod m d ≠ u := by
  intro h
  apply requested_residueMod_ne_zero hd
  apply add_left_cancel (a := u)
  simpa using h

theorem card_residue3 (m : ℕ) [NeZero m] : Fintype.card (Residue3 m) = m ^ 3 := by
  simp [Residue3]

theorem card_liftAlphabet : Fintype.card LiftAlphabet = 125 := by
  norm_num [LiftAlphabet]

theorem card_liftAlphabet_pairs : Fintype.card (LiftAlphabet × LiftAlphabet) = 15625 := by
  norm_num [Fintype.card_prod, card_liftAlphabet]

def liftDifference (m : ℕ) (d : Lattice 3) (u v : Residue3 m) : Lattice 3 :=
  fun i => (d i - (can v i - can u i)) / (m : ℤ)

theorem liftDifference_eq {m : ℕ} [NeZero m] {d : Lattice 3} {u v : Residue3 m}
    (hv : v = u + residueMod m d) (i : Fin 3) :
    (m : ℤ) * liftDifference m d u v i = d i - (can v i - can u i) := by
  apply Int.mul_ediv_cancel'
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
  have hvi := congrFun hv i
  change v i = u i + (d i : ZMod m) at hvi
  simp only [Int.cast_sub, can, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hvi]
  ring

theorem liftDifference_bounds {m : ℕ} [NeZero m] {d : Lattice 3} {u v : Residue3 m}
    (hd : Requested m d) (hv : v = u + residueMod m d) (i : Fin 3) :
    -1 ≤ liftDifference m d u v i ∧ liftDifference m d u v i ≤ 1 := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hdu := (abs_le.mp (hd.1 i)).1
  have hdv := (abs_le.mp (hd.1 i)).2
  have hu0 := can_nonneg u i
  have hv0 := can_nonneg v i
  have hum := can_lt u i
  have hvm := can_lt v i
  have heq := liftDifference_eq hv i
  constructor
  · by_contra h
    have hz : liftDifference m d u v i ≤ -2 := by omega
    have hmz := mul_le_mul_of_nonneg_left hz (le_of_lt hm)
    nlinarith
  · by_contra h
    have hz : 2 ≤ liftDifference m d u v i := by omega
    have hmz := mul_le_mul_of_nonneg_left hz (le_of_lt hm)
    nlinarith

end PeriodicTilingThree

end OAI

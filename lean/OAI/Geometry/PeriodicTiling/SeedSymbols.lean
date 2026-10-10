import OAI.Geometry.PeriodicTiling.EncodingParameters
import OAI.Geometry.PeriodicTiling.LastDigit

namespace OAI

noncomputable section

namespace PeriodicTilingThree

def seedSymbol {p : ℕ} [NeZero p] (E : EncodingParameters p) (t : Fin 2) : Symbol p :=
  lastDigit p E.p_prime ((t.val : ℤ) + 1)

variable {p : ℕ} [NeZero p] (E : EncodingParameters p)

@[simp] theorem seedSymbol_coe (t : Fin 2) :
    (seedSymbol E t : ZMod p) = (t.val : ZMod p) + 1 := by
  have hlt : t.val + 1 < p := by
    have ht := t.isLt
    have hp := E.p_large
    omega
  have hnot : ¬ (p : ℤ) ∣ (t.val : ℤ) + 1 := by
    intro h
    apply Nat.not_dvd_of_pos_of_lt (Nat.succ_pos t.val) hlt
    apply Int.natCast_dvd_natCast.mp
    simpa only [Nat.cast_succ] using h
  simpa only [seedSymbol, Int.cast_add, Int.cast_natCast, Int.cast_one] using
    lastDigit_eq_of_not_dvd p E.p_prime hnot

theorem seedSymbol_injective : Function.Injective (seedSymbol E) := by
  intro s t h
  apply Fin.ext
  have hcoe : (seedSymbol E s : ZMod p) = (seedSymbol E t : ZMod p) :=
    congrArg (fun u : Symbol p => (u : ZMod p)) h
  rw [seedSymbol_coe, seedSymbol_coe] at hcoe
  have hcast : (s.val : ZMod p) = (t.val : ZMod p) := add_right_cancel hcoe
  have hmod := (ZMod.natCast_eq_natCast_iff' s.val t.val p).mp hcast
  have hp : 2 < p := by have := E.p_large; omega
  rw [Nat.mod_eq_of_lt (lt_trans s.isLt hp),
    Nat.mod_eq_of_lt (lt_trans t.isLt hp)] at hmod
  exact hmod

@[simp] theorem seedSymbol_eq_iff {s t : Fin 2} :
    seedSymbol E s = seedSymbol E t ↔ s = t :=
  ⟨fun h => seedSymbol_injective E h, fun h => congrArg (seedSymbol E) h⟩

theorem seedSymbol_ne {s t : Fin 2} (h : s ≠ t) :
    seedSymbol E s ≠ seedSymbol E t :=
  fun hst => h (seedSymbol_injective E hst)

@[simp] theorem seedSymbol_zero : seedSymbol E 0 = 1 := by
  simp [seedSymbol]

@[simp] theorem seedSymbol_one_coe : (seedSymbol E 1 : ZMod p) = 2 := by
  change (lastDigit p E.p_prime 2 : ZMod p) = 2
  exact lastDigit_two p E.p_prime (by have := E.p_large; omega)

theorem seedSymbol_zero_ne_one : seedSymbol E 0 ≠ seedSymbol E 1 :=
  seedSymbol_ne E (by decide)

end PeriodicTilingThree

end

end OAI

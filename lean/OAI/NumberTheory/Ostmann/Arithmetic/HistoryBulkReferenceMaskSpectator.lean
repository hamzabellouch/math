import Mathlib.Data.ZMod.Units
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRTResidue

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkReferenceMask
open Construction HistorySignedSpectatorCRT

theorem residueLeaf_zero_of_giant_cast_zero
    (g : (q : ℕ) → ZMod q → ℂ) (outside : List ℕ) (N : ℕ)
    (a : State) (Xp Xm : ZMod N) (q : ℕ) (hq : q ∈ outside)
    (hg : g q 0 = 0)
    (hz : (ZMod.cast Xp : ZMod q) = 0 ∨ (ZMod.cast Xm : ZMod q) = 0) :
    residueLeaf g outside N a Xp Xm = 0 := by
  apply List.prod_eq_zero_iff.mpr
  apply List.mem_map.mpr
  refine ⟨q, hq, ?_⟩
  rcases hz with hz | hz <;> simp only [hz, zero_mul, mul_zero, ZMod.inv_zero, hg]

theorem residueSpectator_zero_of_giant_cast_zero
    (g : (q : ℕ) → ZMod q → ℂ) (outside : List ℕ) (N : ℕ)
    {l : ℕ} (h : History l) (q : ℕ) (hq : q ∈ outside) (hg : g q 0 = 0)
    (Xp Xm : ZMod N)
    (hz : (ZMod.cast Xp : ZMod q) = 0 ∨ (ZMod.cast Xm : ZMod q) = 0) :
    residueSpectator g outside N h Xp Xm = 0 := by
  induction h generalizing Xp Xm with
  | leaf a => exact residueLeaf_zero_of_giant_cast_zero g outside N a Xp Xm q hq hg hz
  | node a p u hp hm left right il ir =>
    rcases hz with hz | hz
    · rw [residueSpectator, il _ Xp (Or.inr hz), zero_mul]
    · rw [residueSpectator, ir _ Xm (Or.inr hz), map_zero, mul_zero]

theorem residuePairSpectator_nonzero_outsideCoprime
    (g : (q : ℕ) → ZMod q → ℂ) (outside : List ℕ) (N : ℕ)
    (hd : ∀ q ∈ outside, q ∣ N)
    (hprime : ∀ q ∈ outside, q.Prime) (hg : ∀ q ∈ outside, g q 0 = 0)
    {l : ℕ} (h k : History l) (P Q : ℤ)
    (hz : residuePairSpectator g outside N h k (P,Q) ≠ 0) :
    ∀ q ∈ outside, Nat.Coprime P.natAbs q ∧ Nat.Coprime Q.natAbs q := by
  intro q hq
  let : Fact q.Prime := ⟨hprime q hq⟩
  have hne : (P : ZMod q) ≠ 0 ∧ (Q : ZMod q) ≠ 0 := by
    constructor
    · intro hzero
      apply hz
      have hv := residueSpectator_zero_of_giant_cast_zero g outside N h q hq (hg q hq)
        (P : ZMod N) (Q : ZMod N)
        (Or.inl (by simpa only [ZMod.cast_intCast (hd q hq)] using hzero))
      simp only [residuePairSpectator, hv, zero_mul]
    · intro hzero
      apply hz
      have hv := residueSpectator_zero_of_giant_cast_zero g outside N h q hq (hg q hq)
        (P : ZMod N) (Q : ZMod N)
        (Or.inr (by simpa only [ZMod.cast_intCast (hd q hq)] using hzero))
      simp only [residuePairSpectator, hv, zero_mul]
  have hcop (z : ℤ) (hne : (z : ZMod q) ≠ 0) : Nat.Coprime z.natAbs q := by
    have hc := (ZMod.coe_int_isUnit_iff_isCoprime z q).mp (isUnit_iff_ne_zero.mpr hne)
    simpa only [Int.natAbs_natCast] using (Int.isCoprime_iff_nat_coprime.mp hc).symm
  exact ⟨hcop P hne.1, hcop Q hne.2⟩

theorem residuePairSpectator_nonzero_outsideCoprime_prod
    (g : (q : ℕ) → ZMod q → ℂ) (outside : List ℕ)
    (hprime : ∀ q ∈ outside, q.Prime) (hg : ∀ q ∈ outside, g q 0 = 0)
    {l : ℕ} (h k : History l) (P Q : ℤ)
    (hz : residuePairSpectator g outside outside.prod h k (P,Q) ≠ 0) :
    ∀ q ∈ outside, Nat.Coprime P.natAbs q ∧ Nat.Coprime Q.natAbs q :=
  residuePairSpectator_nonzero_outsideCoprime g outside outside.prod
    (fun _ hq => List.dvd_prod hq) hprime hg h k P Q hz

end Ostmann.Arithmetic.HistoryBulkReferenceMask

end

end OAI

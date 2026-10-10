import Mathlib
import OAI.Computability.QuantumFactoring.TableTotient

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring

/-- The finite-word accumulator semantics. Only the multiplicative
accumulator is reduced; division of the residual never overflows. -/
def totientStepNat (B p : ℕ) (s : ℕ×ℕ) : ℕ×ℕ :=
  if p ∣ s.1 then (s.1/p,(s.2*(if p ∣ s.1/p then p else p-1))%B) else s

def totientFoldNat (B : ℕ) : List ℕ → (ℕ×ℕ) → (ℕ×ℕ)
  | [], s => s
  | p::ps, s => totientFoldNat B ps (totientStepNat B p s)

lemma totientStepNat_bound {B p : ℕ} (hB : 0 < B) (s : ℕ×ℕ)
    (hs : s.1 < B ∧ s.2 < B) :
    (totientStepNat B p s).1 < B ∧ (totientStepNat B p s).2 < B := by
  unfold totientStepNat
  split
  · exact ⟨(Nat.div_le_self _ _).trans_lt hs.1,Nat.mod_lt _ hB⟩
  · exact hs

lemma totientFoldNat_score (B : ℕ) (ps : List ℕ) (s : ℕ×ℕ) (hs : s.2 < B) :
    (totientFoldNat B ps s).2=(s.2*totientScan ps s.1)%B := by
  induction ps generalizing s with
  | nil=>simp only [totientFoldNat,totientScan,mul_one,Nat.mod_eq_of_lt hs]
  | cons p ps ih=>
    rw [totientFoldNat,ih (totientStepNat B p s) (by
      unfold totientStepNat
      split
      · exact Nat.mod_lt _ (Nat.zero_lt_of_lt hs)
      · exact hs)]
    rw [totientScan]
    unfold totientStepNat
    split_ifs with hd hp
    · simp only [Nat.mod_mul_mod,mul_assoc]
    · simp only [Nat.mod_mul_mod,mul_assoc]
    · rfl

lemma totientFoldNat_exact (B : ℕ) (ps : List ℕ) (v : ℕ)
    (hB : 1 < B) (hv : 0 < v) (hb : v < B)
    (hp : ∀ p∈ps,p.Prime) (hd : v∣ps.prod) :
    (totientFoldNat B ps (v,1)).2=v.totient := by
  rw [totientFoldNat_score B ps (v,1) hB,totientScan_exact ps v hv hp hd,one_mul,
    Nat.mod_eq_of_lt ((Nat.totient_le v).trans_lt hb)]
end ExactQuantumFactoring


end

end OAI

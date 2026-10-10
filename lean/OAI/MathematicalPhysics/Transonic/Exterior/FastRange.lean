import OAI.MathematicalPhysics.Transonic.Exterior.Range

namespace OAI

section
noncomputable section
namespace SepticProfile.FixedInterval

def hornerChunk (Q : ℤ) (a : ℕ → Box) (x : Box) (lo : ℕ) : ℕ → Box → Box
  | 0,b => b
  | n+1,b => add (a lo) (mul Q x (hornerChunk Q a x (lo+1) n b))

lemma hornerChunk_full (Q : ℤ) (a : ℕ → Box) (x : Box) (lo n m : ℕ) :
    hornerChunk Q a x lo n (hornerBox Q a x (lo+n) m)=hornerBox Q a x lo (n+m) := by
  induction n generalizing lo with
  | zero => simp [hornerChunk]
  | succ n ih =>
    rw [Nat.succ_add,hornerChunk,hornerBox]
    rw [show lo+(n+1)=(lo+1)+n by omega,ih]

lemma hornerChunk_step (Q : ℤ) (a : ℕ → Box) (x b tail : Box) (lo n m : ℕ)
    (hb : b=hornerChunk Q a x lo n tail)
    (ht : tail=hornerBox Q a x (lo+n) m) : b=hornerBox Q a x lo (n+m) := by
  rw [hb,ht,hornerChunk_full]

lemma treeSumBox_zero (d : ℕ) (f : ℕ → Box) (a : ℕ)
    (hz : ∀ i, a ≤ i → i < a+2^d → f i=zero) : treeSumBox d f a=zero := by
  induction d generalizing a with
  | zero => exact hz a le_rfl (by norm_num)
  | succ d ih =>
    rw [treeSumBox,ih a (by intro i hi hi';apply hz i hi;rw [pow_succ];omega),
      ih (a+2^d) (by intro i hi hi';apply hz i (by omega);rw [pow_succ];omega)]
    rfl

def fastSumBox : ℕ → ℕ → ℕ → (ℕ → Box) → ℕ → Box
  | 0,lo,hi,f,a => if lo ≤ a ∧ a < hi then f a else zero
  | d+1,lo,hi,f,a => if hi ≤ a ∨ a+2^(d+1) ≤ lo then zero else
    add (fastSumBox d lo hi f a) (fastSumBox d lo hi f (a+2^d))

lemma fastSumBox_eq (d lo hi : ℕ) (f : ℕ → Box) (a : ℕ) :
    fastSumBox d lo hi f a=treeSumBox d (fun i => if lo ≤ i ∧ i < hi then f i else zero) a := by
  induction d generalizing a with
  | zero => rfl
  | succ d ih =>
    rw [fastSumBox]
    split_ifs with h
    · symm
      apply treeSumBox_zero
      intro i hi1 hi2
      rw [ite_eq_right]
      intro hh
      rcases h with h|h <;> omega
    · rw [treeSumBox,ih,ih]

def fastConvBox (Q : ℤ) (d lo hi : ℕ) (a b : ℕ → Box) (n : ℕ) : Box :=
  fastSumBox d lo hi (fun i => mul Q (a i) (b (n-i))) 0

lemma fastConvBox_eq (Q : ℤ) (d lo hi : ℕ) (a b : ℕ → Box) (n : ℕ) :
    fastConvBox Q d lo hi a b n=convBox Q d lo hi a b n := fastSumBox_eq _ _ _ _ _

end SepticProfile.FixedInterval

end
end

end OAI

import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.DPEnvelope

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized
open Finset

variable {V : Type} [Fintype V] {m : ℕ}
def nextEnvelope (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (w : Fin m → ℕ) : Fin m → ℕ :=
  match parent l with | none=>w | some p=>mergeEnvelope w l p (sharedCount bags R l)
omit [Fintype V] in
lemma nextEnvelope_pos (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (w : Fin m → ℕ) (hw : ∀ a,1≤w a) :
    ∀ a,1≤nextEnvelope bags R parent l w a := by
  cases hp : parent l with
  | none => simpa only [nextEnvelope,hp] using hw
  | some p => simpa only [nextEnvelope,hp] using mergeEnvelope_pos w hw l p (sharedCount bags R l)
lemma nextEnvelope_product (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (w : Fin m → ℕ)
    (hp : ∀ p,parent l=some p → p≠l) :
    (∏ a,nextEnvelope bags R parent l w a)≤2^(Fintype.card V)*(∏ a,w a) := by
  cases he : parent l with
  | none =>
    simp only [nextEnvelope,he]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  | some p =>
    simp only [nextEnvelope,he]
    rw [mergeEnvelope_prod w l p (hp p he)]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (sharedCount_le_card bags R l))
lemma nextEnvelope_power (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (w : Fin m → ℕ)
    (hp : ∀ p,parent l=some p → p≠l) (E : ℕ) (he : (∏ a,w a)≤2^E) :
    (∏ a,nextEnvelope bags R parent l w a)≤2^(E+Fintype.card V) := by
  apply (nextEnvelope_product bags R parent l w hp).trans
  rw [pow_add]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (2^(Fintype.card V)) he
lemma entry_size_budget (bags : V → Finset (Fin m)) (R : Finset V)
    (parent : Fin m → Option (Fin m)) (l : Fin m) (t : Table) (w : Fin m → ℕ)
    (hw : ∀ a,1≤w a) (ht : RowBound t w)
    (hp : ∀ p,parent l=some p → p≠l) (E K : ℕ) (he : (∏ a,w a)≤2^E)
    (hK : E+Fintype.card V+1≤K) (a : Fin m) (r : ℕ) :
    (entry bags R parent l a t r).size≤K := by
  have hv:=nextEnvelope_pos bags R parent l w hw
  have hb : entry bags R parent l a t r≤nextEnvelope bags R parent l w a := by
    cases h : parent l <;> simpa only [nextEnvelope,h] using entry_rowBound bags R parent l t w hw ht a r
  have hprod:=nextEnvelope_power bags R parent l w hp E he
  have hval : entry bags R parent l a t r≤2^(E+Fintype.card V) :=
    hb.trans ((single_le_prod (fun x _=>hv x) (mem_univ a)).trans hprod)
  exact ((Nat.size_le_size hval).trans_eq (Nat.size_pow)).trans hK
end MatchingFPRAS.UnitRefresh.Materialized

end OAI

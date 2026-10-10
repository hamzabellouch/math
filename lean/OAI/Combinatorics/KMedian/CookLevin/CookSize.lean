import Mathlib
import OAI.Combinatorics.KMedian.CookLevin.CookBox
import OAI.Combinatorics.KMedian.CookLevin.InitialSize

namespace OAI

section Inline_PCPCookSize

namespace MetricKMedian.PCP
open Finset
open scoped Classical

namespace Tableau
variable {K : Type} [Fintype K]
def clauseEquiv (T L : ℕ) : Clause (K := K) T L ≃
    ((Fin (T+1) × K × Fin L) ⊕ (Fin (T+1) × K) ⊕ Fin T ⊕ Fin T ⊕ (Fin T × K × Fin (L+1))) where
  toFun
  | .shape t k i => .inl (t,k,i)
  | .end t k => .inr (.inl (t,k))
  | .prefix t => .inr (.inr (.inl t))
  | .control t => .inr (.inr (.inr (.inl t)))
  | .update t k i => .inr (.inr (.inr (.inr (t,k,i))))
  invFun
  | .inl (t,k,i) => .shape t k i
  | .inr (.inl (t,k)) => .end t k
  | .inr (.inr (.inl t)) => .prefix t
  | .inr (.inr (.inr (.inl t))) => .control t
  | .inr (.inr (.inr (.inr (t,k,i)))) => .update t k i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with p|p; rcases p with ⟨a,b,c⟩; rfl; rcases p with p|p; rcases p with ⟨a,b⟩; rfl; rcases p with p|p; rfl; rcases p with p|p; rfl; rfl
lemma clause_card (T L : ℕ) : Fintype.card (Clause (K := K) T L)=
    (T+1)*(Fintype.card K*L)+(T+1)*Fintype.card K+T+T+T*(Fintype.card K*(L+1)) := by
  rw [Fintype.card_congr (clauseEquiv (K := K) T L)]
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega
lemma total_clause_bound (T L : ℕ) :
    Fintype.card (Clause (K := K) T L ⊕ BoundaryClause (K := K) L) ≤
      8*(T+1)*(Fintype.card K+1)*(L+1) := by
  rw [Fintype.card_sum,clause_card]
  simp only [BoundaryClause,Fintype.card_prod,Fintype.card_sum,Fintype.card_bool,
    Fintype.card_unit,Fintype.card_fin]
  ring_nf
  omega
end Tableau
namespace CookLevin
open Turing Turing.TM2 Complexity Tableau Polynomial

variable {verify : Word × Word → Bool}
variable (P : TM2ComputableInPolyTime encodePair encodeBit verify) (p : Polynomial ℕ)
local instance : Fintype P.tm.K := P.tm.kFin
local instance : Fintype P.tm.Λ := P.tm.ΛFin
local instance : Fintype P.tm.σ := P.tm.σFin
lemma firstWord_length (x : Word) : (firstWord x).length≤3*x.length+3 := by
  have h := Binary.NatBinary.length_le_height (Nat.lt_two_pow_self (n := x.length)).le
  simp only [firstWord,encodeNat,List.length_append,List.length_replicate,List.length_singleton]
  omega
noncomputable def inputPoly : Polynomial ℕ := 3*X+3+p
noncomputable def timePoly : Polynomial ℕ := P.time.comp (inputPoly p)
noncomputable def spacePoly : Polynomial ℕ := inputPoly p+C (radius P.tm.m)*timePoly P p+1
lemma inputSize_bound (x : Word) : inputSize p x≤(inputPoly p).eval x.length := by
  simpa only [inputSize,inputPoly,eval_add,eval_mul,eval_ofNat,eval_X] using
    Nat.add_le_add_right (firstWord_length x) (p.eval x.length)
lemma time_bound (x : Word) : time P p x≤(timePoly P p).eval x.length := by
  change P.time.eval (inputSize p x)≤_
  rw [timePoly,eval_comp]
  exact polynomial_mono P.time (inputSize_bound p x)
lemma space_bound (x : Word) : space P p x≤(spacePoly P p).eval x.length := by
  have h := Nat.add_le_add (inputSize_bound p x) (Nat.mul_le_mul_left (radius P.tm.m) (time_bound P p x))
  simpa only [space,spacePoly,eval_add,eval_mul,eval_C,eval_one] using Nat.add_le_add_right h 1
noncomputable def testPoly : Polynomial ℕ :=
  8*(timePoly P p+1)*C (Fintype.card P.tm.K+1)*(spacePoly P p+1)
lemma test_bound (x : Word) : Fintype.card (Test P p x)≤(testPoly P p).eval x.length := by
  have ht := time_bound P p x
  have hs := space_bound P p x
  apply (total_clause_bound (K := P.tm.K) (time P p x) (space P p x)).trans
  simp only [testPoly,eval_mul,eval_add,eval_C,eval_one,eval_ofNat]
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right ht 1))) (Nat.add_le_add_right hs 1)
variable [∀ k, Fintype (P.tm.Γ k)]
@[irreducible] noncomputable def alphabetEdgeCoeff : ℕ :=
  Fintype.card (Query P.tm.m)*(4*Nat.card (AlphabetReduction.EdgeSample (Alphabet P)))
lemma box_edges_formula (x : Word) : (box P p x).edges=Fintype.card (Test P p x)*alphabetEdgeCoeff P := by
  rw [box,InitialAlphabet.box_edges,Nat.card_prod,alphabetEdgeCoeff,← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card]
  exact Nat.mul_assoc _ _ _
noncomputable def edgePoly : Polynomial ℕ := testPoly P p*C (alphabetEdgeCoeff P)
lemma box_edges_bound (x : Word) : (box P p x).edges≤(edgePoly P p).eval x.length := by
  rw [box_edges_formula,edgePoly,eval_mul,eval_C]
  exact Nat.mul_le_mul_right _ (test_bound P p x)
end CookLevin
end MetricKMedian.PCP

end Inline_PCPCookSize

end OAI

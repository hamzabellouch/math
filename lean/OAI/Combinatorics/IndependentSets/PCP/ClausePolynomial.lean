import Mathlib
import OAI.Combinatorics.IndependentSets.Encoding.GapFormula

namespace OAI

namespace LargeIndependentSets
open IndependentSetsGames.Foundations
open scoped Classical
noncomputable section

lemma frame_length (b : List Bool) : (frame b).length = 2*b.length+1 := by
  induction b with
  | nil => rfl
  | cons b bs ih => simp only [frame,List.length_cons,ih]; omega

lemma graphBits_length (G : Graph) : (graphBits G).length = 2*G.vertices.bits.length+1+G.vertices^2 := by
  have h : ∀ vs : List (Fin G.vertices),
      (vs.flatMap (fun u => (List.finRange G.vertices).map (G.adj u))).length =
        vs.length*G.vertices := by
    intro vs
    induction vs with
    | nil => simp
    | cons v vs ih => simp only [List.flatMap_cons,List.length_append,List.length_map,
        List.length_finRange,ih,List.length_cons]; nlinarith
  simp only [graphBits,nameBits,List.length_append,frame_length,h,List.length_finRange,pow_two]

lemma graphBits_bound (G : Graph) : (graphBits G).length ≤ 4*(G.vertices+1)^2 := by
  have h : G.vertices.bits.length ≤ G.vertices := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr G.vertices.lt_two_pow_self
  rw [graphBits_length]
  nlinarith

namespace SemanticReduction
open Target PCP Hastad.SourceContexts Hastad.SourceGame

def clausePolynomial : Polynomial ℕ := TableIteration.formulaBitsPolynomial.comp
  (Polynomial.C 100*(Polynomial.X+Polynomial.C 1)^2)

lemma clauses_bound (H : RoundTables.BaseTable) (F : LargeIndependentSets.Formula) :
    (gapFormula H F).clauses.length ≤ clausePolynomial.eval (LargeIndependentSets.formulaBits F).length := by
  have h0 := Hastad.SourceBounds.formulaBits_length_ge_clauses (gapFormula H F)
  have h1 := TableIteration.gapMap_bits_le H (Normalization.normalize F)
  have h2 := Complexity.MachineComposition.natPolynomial_eval_mono
    TableIteration.formulaBitsPolynomial (Normalization.normalize_bits F)
  apply h0.trans (h1.trans _)
  simpa only [clausePolynomial,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X] using h2

def vertexPolynomial (p : SamplerParameters) (u q : ℕ) : Polynomial ℕ :=
  Polynomial.C q + (Polynomial.C 3 * clausePolynomial)^(u*p.n) *
    Polynomial.C (p.law (J u) (I u)).denominator

lemma vertices_polynomial (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (F : LargeIndependentSets.Formula) :
    (reduce H p u q hq F).vertices ≤
      (vertexPolynomial p u q).eval (LargeIndependentSets.formulaBits F).length := by
  apply (vertex_bound H p u q hq F).trans
  apply (max_le_add_of_nonneg (Nat.zero_le _) (Nat.zero_le _)).trans
  simp only [vertexPolynomial,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
    Polynomial.eval_pow]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_right
  rw [← pow_mul]
  exact Nat.pow_le_pow_left (by nlinarith [clauses_bound H F]) _

def outputPolynomial (p : SamplerParameters) (u q : ℕ) : Polynomial ℕ :=
  Polynomial.C 4*(vertexPolynomial p u q + Polynomial.C 1)^2

lemma output_polynomial (H : RoundTables.BaseTable) (p : SamplerParameters) (u q : ℕ) (hq : 0<q)
    (F : LargeIndependentSets.Formula) :
    (graphBits (reduce H p u q hq F)).length ≤
      (outputPolynomial p u q).eval (LargeIndependentSets.formulaBits F).length := by
  apply (graphBits_bound _).trans
  simp only [outputPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add]
  exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left
    (Nat.add_le_add_right (vertices_polynomial H p u q hq F) 1) 2)

end SemanticReduction

theorem semantic_polynomial_output_reduction {δ : ℚ} (hδ : 0 < δ) :
    ∃ H : PCP.RoundTables.BaseTable, ∃ p : SamplerParameters, ∃ u q : ℕ, ∃ hq : 0 < q,
    ∃ P : Polynomial ℕ,
    (∀ F : Formula, F.Satisfiable → (SemanticReduction.reduce H p u q hq F).ThreeColorable) ∧
    (∀ F : Formula, ¬F.Satisfiable →
      ((SemanticReduction.reduce H p u q hq F).independenceNumber : ℚ) <
      δ*(SemanticReduction.reduce H p u q hq F).vertices) ∧
    (∀ F : Formula, (graphBits (SemanticReduction.reduce H p u q hq F)).length ≤
      P.eval (formulaBits F).length) := by
  obtain ⟨H,p,u,q,hq,hyes,hno⟩ := semantic_reduction hδ
  exact ⟨H,p,u,q,hq,SemanticReduction.outputPolynomial p u q,hyes,hno,
    SemanticReduction.output_polynomial H p u q hq⟩

end
end LargeIndependentSets

end OAI

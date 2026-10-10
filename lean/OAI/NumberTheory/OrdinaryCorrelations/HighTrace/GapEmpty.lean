import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ZeroExpression
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GapPathCode
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FarBlockPair
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.VerticesInBlock
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Expression

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SignedTrace
open OrdinaryCorrelations.NumericalSubtrees OrdinaryCorrelations.ForestTraversal
open Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ K : ℕ}

lemma gap_empty {primeSlots : ℕ} {Alphabet : Type*} [DecidableEq Alphabet]
    (sign : Fin ℓ → Bool) (c : Fin ℓ × Fin primeSlots → Option Alphabet) :
    PatternExpression.gap h sign c (fun _ : Fin K => none)=SquarefreeExpression.zeroExpression Alphabet K := rfl

namespace FarBlockPair
variable {w : NumericalLine D h ℓ} {hh : 0<h} (F : FarBlockPair w hh K)

abbrev selectedEdge (p : F.selected) : Fin ℓ := (F.witness p.val p.property).edge

structure PathData where
  root₁ : Fin (ℓ+1)
  root₂ : Fin (ℓ+1)
  first : F.selected → GapPathCode ℓ K
  second : F.selected → GapPathCode ℓ K
  first_eval : ∀ p,(PatternExpression.gap h (signBit w.line) w.linePrimeCode (first p)).eval
    (fun q => ((q:ℕ):ℤ))=w.line.offset (F.selectedEdge p).castSucc-w.line.offset root₁
  second_eval : ∀ p,(PatternExpression.gap h (signBit w.line) w.linePrimeCode (second p)).eval
    (fun q => ((q:ℕ):ℤ))=w.line.offset (F.witness p.val p.property).vertex-w.line.offset root₂
  first_earlier : ∀ (p q : F.selected),q.val ∈ (PatternExpression.gap h (signBit w.line) w.linePrimeCode (first p)).support →
    F.selectedEdge q < F.selectedEdge p
  second_absent : ∀ (p q : F.selected),q.val ∉ (PatternExpression.gap h (signBit w.line) w.linePrimeCode (second p)).support

lemma pathData_exists (hne : F.selected.Nonempty) : Nonempty F.PathData := by
  obtain ⟨p₀,hp₀⟩ := hne
  have hfne : (blockEdges F.first).Nonempty :=
    ⟨(F.witness p₀ hp₀).edge,mem_filter.mpr ⟨(F.witness p₀ hp₀).tree,F.edge_in p₀ hp₀⟩⟩
  obtain ⟨c₁,_,hpaths⟩ := block_root_paths F.first F.first_small hfne
  let c₂ := (F.witness p₀ hp₀).vertex
  have hc₂ : w.line.offset c₂ ∈ F.second.walk.support := F.vertex_in p₀ hp₀
  have hfirst (p : F.selected) : ∃ r : GapPathCode ℓ K,
      (PatternExpression.gap h (signBit w.line) w.linePrimeCode r).eval (fun q => ((q:ℕ):ℤ))=
        w.line.offset (F.selectedEdge p).castSucc-w.line.offset c₁ ∧
      ∀ q : F.selected,q.val ∈ (PatternExpression.gap h (signBit w.line) w.linePrimeCode r).support →
        F.selectedEdge q < F.selectedEdge p := by
    have he : F.selectedEdge p ∈ blockEdges F.first := mem_filter.mpr ⟨(F.witness p.val p.property).tree,F.edge_in p.val p.property⟩
    rcases hpaths (F.selectedEdge p) he with heq | ⟨P,hP0,hPL,hPE⟩
    · refine ⟨fun _ => none,?_,?_⟩
      · simp [PatternExpression.gap,SquarefreeExpression.eval,heq]
      · intro q hq; simp [PatternExpression.gap,SquarefreeExpression.support] at hq
    · refine ⟨P.code,?_,?_⟩
      · exact P.expression_eval.trans (by rw [hP0,hPL])
      · intro q hq
        obtain ⟨i,hi⟩ := P.expression_support hq
        have hn : ¬S.IsFixed w.line q.val := (mem_filter.mp (Finset.mem_sdiff.mp (F.far q.property)).1).2.1
        have he := ((unique_occurrence_of_free w.line q.val hn (F.selectedEdge q)
          (F.witness q.val q.property).divides (P.edge i)).mp hi)
        exact he ▸ hPE i
  have hsecond (p : F.selected) : ∃ r : GapPathCode ℓ K,
      (PatternExpression.gap h (signBit w.line) w.linePrimeCode r).eval (fun q => ((q:ℕ):ℤ))=
        w.line.offset (F.witness p.val p.property).vertex-w.line.offset c₂ ∧
      ∀ q : F.selected,q.val ∉ (PatternExpression.gap h (signBit w.line) w.linePrimeCode r).support := by
    rcases block_local_paths F.second F.second_small c₂ (F.witness p.val p.property).vertex
      hc₂ (F.vertex_in p.val p.property) with heq | ⟨P,hP0,hPL,hPV⟩
    · refine ⟨fun _ => none,?_,?_⟩
      · simp [PatternExpression.gap,SquarefreeExpression.eval,heq]
      · intro q; simp [PatternExpression.gap,SquarefreeExpression.support]
    · refine ⟨P.code,?_,?_⟩
      · exact P.expression_eval.trans (by rw [hP0,hPL])
      · intro q hq
        obtain ⟨i,hi⟩ := P.expression_support hq
        exact F.second_path_absent P hPV q.val q.property i hi
  choose first hfirst using hfirst
  choose second hsecond using hsecond
  exact ⟨⟨c₁,c₂,first,second,fun p => (hfirst p).1,fun p => (hsecond p).1,
    fun p => (hfirst p).2,fun p => (hsecond p).2⟩⟩

end FarBlockPair
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI

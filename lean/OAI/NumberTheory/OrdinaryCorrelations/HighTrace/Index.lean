import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Splice
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ZeroExpression
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Constant
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DisconnectedWitness
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BlockGateExists
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GateSelection

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.ForestTraversal OrdinaryCorrelations.Rerooting
open OrdinaryCorrelations.ArithmeticSaving
open Finset Classical SimpleGraph
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t : ℕ}
namespace DisconnectedBlockPair
variable {w : NumericalLine D h ℓ} {hh : 0<h} {a : S.FixedResidues w.line}
    {H : Finset (Fin ℓ)} {F : DisconnectedBlockPair w hh a H L}
namespace GateSelection
variable (g : F.GateSelection)
def index : g.selected↪S.Index := ⟨fun p => p.val.val.val,by
  intro p q he
  exact Subtype.ext (Subtype.ext (Subtype.ext he))⟩
structure PathData where
  first : g.selected→GapPathCode ℓ L
  second : g.selected→GapPathCode ℓ L
  first_eval : ∀ p,(PatternExpression.gap h (signBit w.line) w.linePrimeCode (first p)).eval
    (fun q => ((q:ℕ):ℤ))=(g.first p).vertex-g.root₁
  second_eval : ∀ p,(PatternExpression.gap h (signBit w.line) w.linePrimeCode (second p)).eval
    (fun q => ((q:ℕ):ℤ))=(g.second p).vertex-g.root₂
  first_earlier : ∀ p q,g.index q ∈ (PatternExpression.gap h (signBit w.line) w.linePrimeCode (first p)).support →
    g.key q<g.key p
  second_earlier : ∀ p q,g.index q ∈ (PatternExpression.gap h (signBit w.line) w.linePrimeCode (second p)).support →
    g.key q<g.key p

lemma pathData_exists (huncut : w.line.treeSteps\H ⊆ uncutTreeEdges w.line a)
    (hcut : ∀ (P : TreePath w L) (p : S.FixedIndex w.line),P.IsGap a p → ∃ i,P.edge i ∈ H)
    (hph : ∀ p : F.selected,¬(p.val.val:ℕ) ∣ h) : Nonempty g.PathData := by
  have hf (p : g.selected) := block_gate_code w hh a H huncut hcut F.first F.first_small
    (fun p : g.selected => p.val.val) (fun p => hph p.val) g.root₁_in g.root₁_mem g.first p
  have hs (p : g.selected) := block_gate_code w hh a H huncut hcut F.second F.second_small
    (fun p : g.selected => p.val.val) (fun p => hph p.val) g.root₂_in g.root₂_mem g.second p
  choose first hfirst using hf
  choose second hsecond using hs
  exact ⟨⟨first,second,fun p => (hfirst p).1,fun p => (hsecond p).1,
    fun p q hq => g.earlier q p (Or.inl ((hfirst p).2 q hq)),
    fun p q hq => g.earlier q p (Or.inr ((hsecond p).2 q hq))⟩⟩

structure OrderedSelection (t : ℕ) where
  pick : Fin t ↪ g.selected
  key_mono : ∀ {i j : Fin t},i ≤ j → g.key (pick i) ≤ g.key (pick j)
lemma orderedSelection_exists (ht : t ≤ g.selected.card) : Nonempty (g.OrderedSelection t) := by
  let key : g.selected→(ℕ ×ₗ S.Index) := fun p => toLex (g.key p,g.index p)
  have hk : Function.Injective key := by
    intro p q he
    exact g.index.injective (congrArg (fun z => (ofLex z).2) he)
  let I := (univ : Finset g.selected).image key
  have hI : I.card=g.selected.card := by
    rw [card_image_iff.mpr (fun p hp q hq he => hk he)]
    simp
  let f : Fin g.selected.card↪o (ℕ ×ₗ S.Index) := I.orderEmbOfFin hI
  have hpre (i : Fin g.selected.card) : ∃ p : g.selected,key p=f i := by
    obtain ⟨p,hp,he⟩ := mem_image.mp (I.orderEmbOfFin_mem hI i)
    exact ⟨p,he⟩
  choose q hq using hpre
  let p : Fin t ↪ g.selected := {
    toFun i := q (Fin.castLE ht i)
    inj' := by
      intro i j he
      have he' := congrArg key he
      change key (q (Fin.castLE ht i))=key (q (Fin.castLE ht j)) at he'
      rw [hq,hq] at he'
      exact Fin.ext (congrArg (fun x : Fin g.selected.card => x.val) (f.injective he')) }
  refine ⟨⟨p,?_⟩⟩
  intro i j hij
  have he := f.monotone (show Fin.castLE ht i ≤ Fin.castLE ht j from hij)
  rw [←hq,←hq] at he
  exact (Prod.Lex.toLex_le_toLex'.mp he).1

namespace PathData
variable {g} (d : g.PathData)
def rootOffset (_d : g.PathData) : ℤ := g.root₂-g.root₁
def firstExpression (p : g.selected) := PatternExpression.gap h (signBit w.line) w.linePrimeCode (d.first p)
def secondExpression (p : g.selected) := PatternExpression.gap h (signBit w.line) w.linePrimeCode (d.second p)
def expression (p : g.selected) : SquarefreeExpression S.Index ((1+L)+L) :=
  ((SquarefreeExpression.constant d.rootOffset).append (d.firstExpression p).neg).append (d.secondExpression p)
lemma expression_eval (p : g.selected) : (d.expression p).eval (fun q => ((q:ℕ):ℤ))=
    (g.second p).vertex-(g.first p).vertex := by
  simp only [expression,SquarefreeExpression.eval_append,SquarefreeExpression.eval_constant,SquarefreeExpression.eval_neg]
  rw [show (d.firstExpression p).eval (fun q => ((q:ℕ):ℤ))=_ from d.first_eval p,
    show (d.secondExpression p).eval (fun q => ((q:ℕ):ℤ))=_ from d.second_eval p]
  dsimp [rootOffset]
  ring
lemma expression_nonzero
    (hcut : ∀ (P : TreePath w L) (p : S.FixedIndex w.line),P.IsGap a p → ∃ i,P.edge i ∈ H)
    (hph : ∀ p : F.selected,¬(p.val.val:ℕ) ∣ h) (p : g.selected) :
    (d.expression p).eval (fun q => ((q:ℕ):ℤ))≠0 := by
  rw [d.expression_eval]
  apply sub_ne_zero.mpr
  intro he
  have hn := F.active_separate hcut p.val (hph p.val) (g.first p).mem (g.second p).mem
  apply hn
  rw [he]
lemma expression_divides (p : g.selected) : ((g.index p:ℕ):ℤ) ∣ (d.expression p).eval (fun q => ((q:ℕ):ℤ)) := by
  rw [d.expression_eval]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [Int.cast_sub]
  apply sub_eq_zero.mpr
  have he := (mem_filter.mp (g.second p).mem).2.2.trans (mem_filter.mp (g.first p).mem).2.2.symm
  change ((g.second p).vertex : ZMod (p.val.val.val:ℕ))=((g.first p).vertex : ZMod (p.val.val.val:ℕ))
  exact add_left_cancel he
lemma expression_earlier (p q : g.selected) (hq : g.index q ∈ (d.expression p).support) :
    g.key q<g.key p := by
  simp only [expression,SquarefreeExpression.support_append,SquarefreeExpression.support_constant,
    SquarefreeExpression.support_neg,empty_union,mem_union] at hq
  rcases hq with hq|hq
  · exact d.first_earlier p q hq
  · exact d.second_earlier p q hq
variable (s : g.OrderedSelection t)
def selected : Fin t↪S.Index := s.pick.trans g.index
def tests : TriangularExpressions (selected s) ((1+L)+L) where
  expression i := d.expression (s.pick i)
  modulus := selected s
  linear _ := false
  divisor_modulus _ _ := rfl
  divisor_own_absent i _ := by
    intro hi
    exact (lt_irrefl _) (d.expression_earlier (s.pick i) (s.pick i) hi)
  linear_modulus_ne _ hi := Bool.noConfusion hi
  future_absent i j hij := by
    intro hj
    rcases mem_insert.mp hj with heq|he
    · exact (ne_of_gt hij) ((selected s).injective heq)
    · exact (not_lt_of_ge (s.key_mono hij.le)) (d.expression_earlier (s.pick i) (s.pick j) he)

end PathData
end GateSelection
end DisconnectedBlockPair
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI

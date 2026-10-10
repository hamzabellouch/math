import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ZeroExpression
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GapPathCode
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GapEmpty
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Constant

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
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ K t : ℕ}
namespace FarBlockPair
variable {w : NumericalLine D h ℓ} {hh : 0<h} (F : FarBlockPair w hh K)

structure OrderedSelection (t : ℕ) where
  pick : Fin t ↪ F.selected
  edge_mono : Monotone (fun i => F.selectedEdge (pick i))

lemma orderedSelection_exists (ht : t ≤ F.selected.card) : Nonempty (F.OrderedSelection t) := by
  let key : F.selected → (Fin ℓ ×ₗ S.Index) := fun p => toLex (F.selectedEdge p,p.val)
  have hk : Function.Injective key := by
    intro p q he
    apply Subtype.ext
    exact congrArg (fun z => (ofLex z).2) he
  let I := (univ : Finset F.selected).image key
  have hI : I.card=F.selected.card := by
    rw [card_image_iff.mpr (fun p _ q _ he => hk he)]
    simp
  let f : Fin F.selected.card ↪o (Fin ℓ ×ₗ S.Index) := I.orderEmbOfFin hI
  have hpre (i : Fin F.selected.card) : ∃ p : F.selected,key p=f i := by
    obtain ⟨p,_,he⟩ := mem_image.mp (I.orderEmbOfFin_mem hI i)
    exact ⟨p,he⟩
  choose q hq using hpre
  let p : Fin t ↪ F.selected := {
    toFun i := q (Fin.castLE ht i)
    inj' := by
      intro i j he
      have he' := congrArg key he
      change key (q (Fin.castLE ht i))=key (q (Fin.castLE ht j)) at he'
      rw [hq,hq] at he'
      exact Fin.ext (congrArg (fun x : Fin F.selected.card => x.val) (f.injective he')) }
  refine ⟨⟨p,?_⟩⟩
  intro i j hij
  have he := f.monotone (show Fin.castLE ht i ≤ Fin.castLE ht j from hij)
  rw [←hq,←hq] at he
  exact (Prod.Lex.toLex_le_toLex'.mp he).1

namespace PathData
variable {F} (d : F.PathData)
def rootOffset : ℤ := w.line.offset d.root₂-w.line.offset d.root₁
def firstExpression (p : F.selected) := PatternExpression.gap h (signBit w.line) w.linePrimeCode (d.first p)
def secondExpression (p : F.selected) := PatternExpression.gap h (signBit w.line) w.linePrimeCode (d.second p)
def expression (p : F.selected) : SquarefreeExpression S.Index ((1+K)+K) :=
  ((SquarefreeExpression.constant d.rootOffset).append (d.firstExpression p).neg).append (d.secondExpression p)

lemma expression_eval (p : F.selected) : (d.expression p).eval (fun q => ((q:ℕ):ℤ))=
    w.line.offset (F.witness p.val p.property).vertex-w.line.offset (F.selectedEdge p).castSucc := by
  simp only [expression,SquarefreeExpression.eval_append,SquarefreeExpression.eval_constant,SquarefreeExpression.eval_neg]
  rw [show (d.firstExpression p).eval (fun q => ((q:ℕ):ℤ))=_ from d.first_eval p,
    show (d.secondExpression p).eval (fun q => ((q:ℕ):ℤ))=_ from d.second_eval p]
  dsimp [rootOffset]
  ring
lemma expression_nonzero (p : F.selected) : (d.expression p).eval (fun q => ((q:ℕ):ℤ))≠0 := by
  rw [d.expression_eval]
  exact sub_ne_zero.mpr (F.witness p.val p.property).left_ne
lemma expression_divides (p : F.selected) : ((p.val:ℕ):ℤ) ∣ (d.expression p).eval (fun q => ((q:ℕ):ℤ)) := by
  rw [d.expression_eval]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  rw [Int.cast_sub]
  exact sub_eq_zero.mpr (F.witness p.val p.property).congruent
lemma expression_earlier (p q : F.selected) (hq : q.val ∈ (d.expression p).support) :
    F.selectedEdge q < F.selectedEdge p := by
  simp only [expression,SquarefreeExpression.support_append,SquarefreeExpression.support_constant,
    SquarefreeExpression.support_neg,empty_union,mem_union] at hq
  rcases hq with hq | hq
  · exact d.first_earlier p q hq
  · exact (d.second_absent p q hq).elim

variable (s : F.OrderedSelection t)
def selected : Fin t ↪ S.Index := ⟨fun i => (s.pick i).val,by
  intro i j he; exact s.pick.injective (Subtype.ext he)⟩
def tests : TriangularExpressions (selected s) ((1+K)+K) where
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
    rcases mem_insert.mp hj with heq | he
    · exact (ne_of_gt hij) ((selected s).injective heq)
    · exact (not_lt_of_ge (s.edge_mono hij.le)) (d.expression_earlier (s.pick i) (s.pick j) he)

end PathData

end FarBlockPair
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI

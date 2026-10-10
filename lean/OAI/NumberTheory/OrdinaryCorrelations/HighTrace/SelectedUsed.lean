import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RootCode
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Index

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ArithmeticSaving OrdinaryCorrelations.SharedSlotPatterns
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L t R : ℕ}
namespace DisconnectedBlockPair.GateSelection.PathData
variable {w : NumericalLine D h ℓ} {hh : 0<h} {a : S.FixedResidues w.line}
    {H : Finset (Fin ℓ)} {F : DisconnectedBlockPair w hh a H L} {g : F.GateSelection}
    (d : g.PathData) (s : g.OrderedSelection t)
lemma selected_used (i : Fin t) : ∃ e,(selected s i:ℕ) ∣ w.line.label e := by
  obtain ⟨e,he⟩ := F.tree (s.pick i).val.val (s.pick i).val.property
  exact ⟨e,(mem_filter.mp he).2⟩
def selectedIndex (i : Fin t) : Fin (support w.linePrimeCode).card :=
  w.primeIndex (selected s i) (w.used_mem_support _ (selected_used s i))
def template (hr : d.rootOffset.natAbs ≤ R) : FarTemplate ℓ L ⌈C₀*Real.log B⌉₊ t (support w.linePrimeCode).card R :=
  ⟨rootCode d.rootOffset R hr,signBit w.line,pattern w.linePrimeCode,
    fun i => d.first (s.pick i),fun i => d.second (s.pick i),selectedIndex s⟩
lemma root_relabel (hr : d.rootOffset.natAbs ≤ R) : (d.template s hr).root=d.rootOffset := rootCode_decode d.rootOffset R hr
lemma selected_relabel (hr : d.rootOffset.natAbs ≤ R) (i : Fin t) :
    values w.linePrimeCode ((d.template s hr).selected i)=selected s i := w.values_primeIndex _ _
lemma expression_relabel (hr : d.rootOffset.natAbs ≤ R) (i : Fin t) :
    ((d.template s hr).expression h i).relabel (values w.linePrimeCode)=(d.tests s).expression i := by
  change (((SquarefreeExpression.constant (d.template s hr).root).append
    (PatternExpression.gap h (signBit w.line) (pattern w.linePrimeCode) (d.first (s.pick i))).neg).append
    (PatternExpression.gap h (signBit w.line) (pattern w.linePrimeCode) (d.second (s.pick i)))).relabel _=_
  rw [SquarefreeExpression.relabel_append,SquarefreeExpression.relabel_append,
    SquarefreeExpression.constantExpression_relabel,SquarefreeExpression.relabel_neg,PatternExpression.gap_relabel,PatternExpression.gap_relabel]
  simp_rw [decode_pattern]
  rw [d.root_relabel s hr]
  rfl
lemma formed (hr : d.rootOffset.natAbs ≤ R) : (d.template s hr).WellFormed h :=
  (d.template s hr).formed_of_relabel h (values w.linePrimeCode) (selected s) (d.tests s)
    (fun _ => rfl) (d.selected_relabel s hr) (d.expression_relabel s hr)

lemma root_bound (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B) : d.rootOffset.natAbs ≤ farRootBudget B C₀ τ h := by
  have hb := source_line_difference_bound w.line w.labels hτ hℓ g.root₁ g.root₁_mem g.root₂ g.root₂_mem
  change (g.root₂-g.root₁).natAbs ≤ ⌈Real.exp ((C₀+4*(h:ℝ)*τ)*B)⌉₊
  exact Nat.cast_le.mp (hb.trans (Nat.le_ceil _))
lemma admissible
    (hcut : ∀ (P : TreePath w L) (p : S.FixedIndex w.line),P.IsGap a p → ∃ i,P.edge i ∈ H)
    (hph : ∀ p : F.selected,¬(p.val.val:ℕ) ∣ h)
    (P : ℝ) (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B) :
    (d.tests s).Admissible P (farTestSize B C₀ τ h) (fun p => (p:ℕ)) := by
  intro i
  change (ArithmeticClause.divisor ((d.expression (s.pick i)).eval (fun p => ((p:ℕ):ℤ)))).Holds P _ (selected s i:ℕ)
  refine ⟨d.expression_nonzero hcut hph _,?_,d.expression_divides _⟩
  rw [d.expression_eval]
  apply Real.log_le_log (by positivity)
  have hb := source_line_difference_bound w.line w.labels hτ hℓ
    (g.first (s.pick i)).vertex (mem_filter.mp (g.first (s.pick i)).mem).1
    (g.second (s.pick i)).vertex (mem_filter.mp (g.second (s.pick i)).mem).1
  have ha : |(((g.second (s.pick i)).vertex-(g.first (s.pick i)).vertex:ℤ):ℝ)| =
      (((g.second (s.pick i)).vertex-(g.first (s.pick i)).vertex).natAbs:ℝ) := by
    rw [←Int.cast_abs,←Int.natCast_natAbs]
    simp only [Int.cast_natCast]
  rw [ha]
  linarith
lemma template_admissible (hr : d.rootOffset.natAbs ≤ R)
    (hcut : ∀ (P : TreePath w L) (p : S.FixedIndex w.line),P.IsGap a p → ∃ i,P.edge i ∈ H)
    (hph : ∀ p : F.selected,¬(p.val.val:ℕ) ∣ h)
    (P : ℝ) (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B) :
    ((d.template s hr).system h (d.formed s hr)).Admissible P (farTestSize B C₀ τ h)
      (fun i => (values w.linePrimeCode i:ℕ)) := by
  intro i
  change (ArithmeticClause.divisor (((d.template s hr).expression h i).eval
    (fun a => ((values w.linePrimeCode a:ℕ):ℤ)))).Holds P _
      (values w.linePrimeCode ((d.template s hr).selected i):ℕ)
  rw [←SquarefreeExpression.eval_relabel _ (values w.linePrimeCode) (fun p => ((p:ℕ):ℤ)),
    d.expression_relabel,d.selected_relabel]
  exact d.admissible s hcut hph P hτ hℓ i

end DisconnectedBlockPair.GateSelection.PathData
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI

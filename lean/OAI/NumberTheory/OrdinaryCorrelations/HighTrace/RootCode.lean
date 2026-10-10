import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.RelabelAppend
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.GapEmpty
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FarTemplate
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.OrderedSelection

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
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ K t R : ℕ}

def rootCode (k : ℤ) (R : ℕ) (hk : k.natAbs ≤ R) : Fin (2*R+1) :=
  ⟨(k+R).toNat,by
    have ha : |k| ≤ (R:ℤ) := by rw [←Int.natCast_natAbs]; exact_mod_cast hk
    obtain ⟨hl,hr⟩ := abs_le.mp ha
    have hn : 0≤k+R := by omega
    have he := Int.toNat_of_nonneg hn
    omega⟩
lemma rootCode_decode (k : ℤ) (R : ℕ) (hk : k.natAbs ≤ R) : ((rootCode k R hk).val:ℤ)-R=k := by
  have ha : |k| ≤ (R:ℤ) := by rw [←Int.natCast_natAbs]; exact_mod_cast hk
  obtain ⟨hl,hr⟩ := abs_le.mp ha
  have hn : 0≤k+R := by omega
  change ((k+R).toNat:ℤ)-R=k
  rw [Int.toNat_of_nonneg hn]
  omega

def farRootBudget (B C₀ τ : ℝ) (h : ℕ) : ℕ := ⌈Real.exp ((C₀+4*(h:ℝ)*τ)*B)⌉₊
def farTestSize (B C₀ τ : ℝ) (h : ℕ) : ℝ := Real.log (Real.exp ((C₀+4*(h:ℝ)*τ)*B)+2)
lemma farTestSize_nonneg : 0≤farTestSize B C₀ τ h := by
  apply Real.log_nonneg
  have := (Real.exp_pos ((C₀+4*(h:ℝ)*τ)*B)).le
  linarith

namespace FarBlockPair.PathData
variable {w : NumericalLine D h ℓ} {hh : 0<h} {F : FarBlockPair w hh K}
variable (d : F.PathData) (s : F.OrderedSelection t)

def selectedIndex (i : Fin t) : Fin (support w.linePrimeCode).card :=
  w.primeIndex (selected s i) (w.used_mem_support _ ⟨F.selectedEdge (s.pick i),(F.witness _ _).divides⟩)
def template (hr : d.rootOffset.natAbs ≤ R) : FarTemplate ℓ K ⌈C₀*Real.log B⌉₊ t (support w.linePrimeCode).card R :=
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
  have hb := source_line_difference_bound w.line w.labels hτ hℓ
    (w.line.offset d.root₁) (mem_image.mpr ⟨_,mem_univ _,rfl⟩)
    (w.line.offset d.root₂) (mem_image.mpr ⟨_,mem_univ _,rfl⟩)
  change (w.line.offset d.root₂-w.line.offset d.root₁).natAbs ≤ ⌈Real.exp ((C₀+4*(h:ℝ)*τ)*B)⌉₊
  exact Nat.cast_le.mp (hb.trans (Nat.le_ceil _))
lemma admissible (P : ℝ) (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B) :
    (d.tests s).Admissible P (farTestSize B C₀ τ h) (fun p => (p:ℕ)) := by
  intro i
  change (ArithmeticClause.divisor ((d.expression (s.pick i)).eval (fun p => ((p:ℕ):ℤ)))).Holds P _ (selected s i:ℕ)
  refine ⟨d.expression_nonzero _,?_,d.expression_divides _⟩
  rw [d.expression_eval]
  apply Real.log_le_log (by positivity)
  have hb := source_line_difference_bound w.line w.labels hτ hℓ
    (w.line.offset (F.selectedEdge (s.pick i)).castSucc) (mem_image.mpr ⟨_,mem_univ _,rfl⟩)
    (w.line.offset (F.witness (s.pick i).val (s.pick i).property).vertex) (mem_image.mpr ⟨_,mem_univ _,rfl⟩)
  have ha : |((w.line.offset (F.witness (s.pick i).val (s.pick i).property).vertex-
      w.line.offset (F.selectedEdge (s.pick i)).castSucc:ℤ):ℝ)| =
      ((w.line.offset (F.witness (s.pick i).val (s.pick i).property).vertex-
      w.line.offset (F.selectedEdge (s.pick i)).castSucc).natAbs:ℝ) := by
    rw [←Int.cast_abs,←Int.natCast_natAbs]
    simp only [Int.cast_natCast]
  rw [ha]
  linarith
lemma template_admissible (hr : d.rootOffset.natAbs ≤ R) (P : ℝ) (hτ : 0≤τ) (hℓ : (ℓ:ℝ) ≤ 2*B) :
    ((d.template s hr).system h (d.formed s hr)).Admissible P (farTestSize B C₀ τ h)
      (fun i => (values w.linePrimeCode i:ℕ)) := by
  intro i
  change (ArithmeticClause.divisor (((d.template s hr).expression h i).eval
    (fun a => ((values w.linePrimeCode a:ℕ):ℤ)))).Holds P _
      (values w.linePrimeCode ((d.template s hr).selected i):ℕ)
  rw [←SquarefreeExpression.eval_relabel _ (values w.linePrimeCode) (fun p => ((p:ℕ):ℤ)),
    d.expression_relabel,d.selected_relabel]
  exact d.admissible s P hτ hℓ i

end FarBlockPair.PathData
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI

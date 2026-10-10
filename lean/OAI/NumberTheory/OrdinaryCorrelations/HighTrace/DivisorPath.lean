import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SpecificationTemplate
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UncutTreeEdges
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IndependentTests

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.ArithmeticSaving Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ K : ℕ}

structure DivisorPath (w : NumericalLine D h ℓ) (p : S.Index) (K : ℕ) where
  path : TreePath w K
  absent : ∀ i,¬(p:ℕ) ∣ w.line.label (path.edge i)
  divides : ((p:ℕ):ℤ) ∣ path.vertex (Fin.last path.length)-path.vertex 0

namespace DivisorPath
variable {w : NumericalLine D h ℓ} {p : S.Index} (d : DivisorPath w p K)
def spec : S.Specification D h K := d.path.specification p d.absent d.divides
def expression : SquarefreeExpression S.Index K := d.spec.segmentExpression 0 d.path.length
lemma extra_absent : p ∉ d.expression.support := d.spec.segmentExpression_extra_absent 0 d.path.length
lemma eval : d.expression.eval (fun q => ((q:ℕ):ℤ)) =
    d.path.vertex (Fin.last d.path.length)-d.path.vertex 0 := by
  rw [expression,d.spec.segmentExpression_eval 0 d.path.length (Nat.zero_le _) le_rfl]
  simp [spec,TreePath.specification,Fin.last]
lemma nonzero : d.expression.eval (fun q => ((q:ℕ):ℤ)) ≠ 0 := by
  rw [d.eval]
  intro hz
  have he := congrArg Fin.val (d.path.distinct (sub_eq_zero.mp hz))
  have hp := d.path.length_pos
  simp only [Fin.val_last,Fin.val_zero] at he
  omega
lemma support_card : d.expression.support.card ≤ K*⌈C₀*Real.log B⌉₊ := by
  change (univ.biUnion (fun i => if d.expression.coefficient i=0 then ∅ else d.expression.factors i)).card ≤ _
  apply (card_biUnion_le_card_mul univ _ ⌈C₀*Real.log B⌉₊ ?_).trans
  · simp
  · intro i hi
    split_ifs
    · simp
    · exact d.spec.segmentExpression_factor_card 0 d.path.length i
lemma numeric_holds (P : ℝ) (hB : 0≤B) (hS : ∀ q : S.Index,(q:ℝ) ≤ Real.exp B) :
    (ArithmeticClause.divisor (d.expression.eval (fun q => ((q:ℕ):ℤ)))).Holds P
      (Specification.densitySize B C₀ h K) (p:ℕ) := by
  refine ⟨d.nonzero,?_,?_⟩
  · exact d.spec.suffix_log_size hB hS
  · rw [d.eval]; exact d.divides
end DivisorPath

def shortCorrupted (w : NumericalLine D h ℓ) (K : ℕ) : Finset S.Index :=
  univ.filter (fun p => freeCorrupted w.line p ∧ Nonempty (DivisorPath w p K))

namespace NumericalLine
variable (w : NumericalLine D h ℓ)

def shortCorruptPath (p : {p // p ∈ shortCorrupted w K}) : DivisorPath w p.val K :=
  Classical.choice (mem_filter.mp p.property).2.2

structure ShortCorruptSelection (K t : ℕ) where
  selected : Fin t ↪ S.Index
  used : ∀ i,∃ e,(selected i:ℕ) ∣ w.line.label e
  path : ∀ i, DivisorPath w (selected i) K
  independent : ∀ i j,selected j ∉ (path i).expression.support

lemma shortCorruptSelection_exists (K t : ℕ)
    (hcount : (2*(K*⌈C₀*Real.log B⌉₊)+1)*t ≤ (shortCorrupted w K).card) :
    Nonempty (w.ShortCorruptSelection K t) := by
  let A := shortCorrupted w K
  let f : A → S.Index := Subtype.val
  let test : ∀ p : A,DivisorPath w (f p) K := w.shortCorruptPath
  let R (p q : A) : Prop := q.val ∈ (test p).expression.support
  have hout (p : A) (hp : p ∈ (univ : Finset A)) :
      (univ.filter (R p)).card ≤ K*⌈C₀*Real.log B⌉₊ := by
    apply le_trans _ (test p).support_card
    apply card_le_card_of_injOn Subtype.val
    · intro q hq
      exact (mem_filter.mp hq).2
    · intro q hq r hr he
      exact Subtype.ext he
  obtain ⟨I,hI,hsize,hi⟩ := independent_tests R (K*⌈C₀*Real.log B⌉₊) (univ : Finset A) (by
    intro a ha
    convert hout a ha using 1
    congr 1
    ext q
    simp only [mem_filter])
  have ht : t ≤ I.card := by
    have hA : (univ : Finset A).card=A.card := by simp
    rw [hA] at hsize
    have hc : (2*(K*⌈C₀*Real.log B⌉₊)+1)*t ≤ (2*(K*⌈C₀*Real.log B⌉₊)+1)*I.card := hcount.trans hsize
    exact Nat.le_of_mul_le_mul_left hc (by omega)
  obtain ⟨e⟩ := (Function.Embedding.nonempty_iff_card_le).mpr (show Fintype.card (Fin t) ≤ Fintype.card I by simpa using ht)
  let sel : Fin t ↪ S.Index := {
    toFun i := (e i).val.val
    inj' := by intro i j hij; apply e.injective; apply Subtype.ext; exact Subtype.ext hij }
  refine ⟨⟨sel,?_,fun i => test (e i).val,?_⟩⟩
  · intro i
    obtain ⟨hn,k,hk,hw⟩ := (mem_filter.mp (e i).val.property).2.1
    exact ⟨k,(mem_filter.mp hk).2⟩
  · intro i j
    by_cases hij : i=j
    · subst j
      exact (test (e i).val).extra_absent
    · exact hi (e i).val (e i).property (e j).val (e j).property
        (by intro he; apply hij; exact e.injective (Subtype.ext he))

end NumericalLine
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI

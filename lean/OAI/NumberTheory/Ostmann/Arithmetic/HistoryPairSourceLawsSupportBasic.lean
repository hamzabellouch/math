import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairScaledKernelReplacementSources
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLaws

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CompensationEqualityPatterns HistoryPairKernelReplacement
attribute [local instance] Classical.propDecidable

def PositiveSourceValue (S : PrimeSource) (z : ℤ) : Prop :=
  ∃ v : S.Sample, z = (v.val : ℤ) ∧ S.law.mass v ≠ 0

theorem integerWeight_ne_zero {κ : Type*} [Fintype κ]
    (value : κ → ℤ) (w : κ → ℝ) {z : ℤ} (hz : integerWeight value w z ≠ 0) :
    ∃ a, z = value a ∧ w a ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  apply hz
  unfold integerWeight
  apply Finset.sum_eq_zero
  intro a ha
  split_ifs with he
  · exact hn a he.symm
  · rfl

theorem positiveSourceValue_of_integerWeight (S : PrimeSource) {z : ℤ}
    (hz : integerWeight (fun v : S.Sample => (v.val : ℤ)) S.law.mass z ≠ 0) :
    PositiveSourceValue S z := integerWeight_ne_zero _ _ hz

theorem PositiveSourceValue.sourceMass {sources : SourceFamily} {q : SmallSlot} {z : ℤ}
    (hz : PositiveSourceValue (sources q.origin) z) :
    ∃ n : ℕ, z = (n : ℤ) ∧ sourceMass sources (resampledSlot q n) ≠ 0 := by
  obtain ⟨v,hv,hm⟩ := hz
  refine ⟨v.val,hv,?_⟩
  change (if h : v.val ∈ (sources q.origin).candidates then
    (sources q.origin).law.mass ⟨v.val,h⟩ else 0) ≠ 0
  simpa only [v.property,dite_true] using hm

theorem biasedBlockWeight_source_nonzero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (q : Block p) (v : CommonSample sources origin)
    (hv : biasedBlockWeight sources origin p q v ≠ 0) (i : Fiber p q) :
    sourceWeight sources origin i.val v ≠ 0 := by
  intro hi
  have hz : blockWeight p (sourceWeight sources origin) q v = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hi
  apply hv
  simp only [biasedBlockWeight,hz,zero_mul,zero_div]

theorem positiveSourceValue_of_sourceWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sources : SourceFamily) (origin : ι → ℕ) (i : ι) (v : CommonSample sources origin)
    (hv : sourceWeight sources origin i v ≠ 0) :
    PositiveSourceValue (sources (origin i)) (v.val : ℤ) := by
  unfold sourceWeight at hv
  split_ifs at hv with hm
  · exact ⟨⟨v.val,hm⟩,rfl,hv⟩
  · exact (hv rfl).elim

theorem positiveSourceValue_of_block_integerWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (q : Block p) {z : ℤ}
    (hz : integerWeight (fun v : CommonSample sources origin => (v.val : ℤ))
      (biasedBlockWeight sources origin p q) z ≠ 0) (i : Fiber p q) :
    PositiveSourceValue (sources (origin i.val)) z := by
  obtain ⟨v,hv,hw⟩ := integerWeight_ne_zero _ _ hz
  rw [hv]
  exact positiveSourceValue_of_sourceWeight sources origin i.val v
    (biasedBlockWeight_source_nonzero sources origin p q v hw i)

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI

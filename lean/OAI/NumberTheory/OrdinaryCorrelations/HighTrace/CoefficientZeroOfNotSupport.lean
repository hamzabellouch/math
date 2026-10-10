import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.VertexAt
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrivateFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SegmentEdges

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ n : ℕ}

lemma Specification.coefficient_zero_of_not_support (s : S.Specification D h L)
    (q : S.Index) (hq : (q:ℕ) ∉ s.primeSupport) (a b : ℕ) : s.coefficient q a b=0 := by
  apply sum_eq_zero
  intro i hi
  unfold Specification.coefficientAt
  split_ifs with hn hd
  · exact (hq ((s.support_iff_extra_or_label q).mpr (Or.inr ⟨⟨i,hn⟩,hd⟩))).elim
  · rfl
  · rfl

namespace PrivateFamily
variable {w : ClosedLine h ℓ} (F : PrivateFamily w D L n)

lemma before_segment_absent (j : Fin n) (hj : F.BeforeLine j)
    (a b : Fin (ℓ+1)) (ha : a ≤ (F.witness j).index) (hb : b ≤ (F.witness j).index) :
    (F.key j:ℕ) ∉ w.segmentSupport a b := by
  intro hm
  obtain ⟨e,he,he',hd⟩ := (w.mem_segmentSupport_iff a b (F.key j)
    (S.prime_mem _ (F.key j).property)).mp hm
  apply hj e _ hd
  have ha' : a.val ≤ (F.witness j).index.val := ha
  have hb' : b.val ≤ (F.witness j).index.val := hb
  omega

lemma after_segment_absent (j : Fin n) (hj : F.AfterLine j)
    (a b : Fin (ℓ+1)) (ha : (F.witness j).index ≤ a) (hb : (F.witness j).index ≤ b) :
    (F.key j:ℕ) ∉ w.segmentSupport a b := by
  intro hm
  obtain ⟨e,he,he',hd⟩ := (w.mem_segmentSupport_iff a b (F.key j)
    (S.prime_mem _ (F.key j).property)).mp hm
  apply hj e _ hd
  have ha' : (F.witness j).index.val ≤ a.val := ha
  have hb' : (F.witness j).index.val ≤ b.val := hb
  omega

noncomputable def comparisonSupport (i j : Fin n) : Finset ℕ :=
  (F.witness i).spec.primeSupport ∪ (F.witness j).spec.primeSupport ∪
    w.segmentSupport (F.witness i).index (F.witness j).index

lemma future_absent_before (i j k : Fin n) (hij : i < j) (hjk : j < k)
    (hk : F.BeforeLine k) : (F.key k:ℕ) ∉ F.comparisonSupport i j := by
  simp only [comparisonSupport,mem_union,not_or]
  exact ⟨⟨F.key_private k i (ne_of_gt (hij.trans hjk)),
    F.key_private k j (ne_of_gt hjk)⟩,
    F.before_segment_absent k hk _ _ (F.ordered (hij.trans hjk).le) (F.ordered hjk.le)⟩

lemma future_absent_after (i j k : Fin n) (hji : j < i) (hkj : k < j)
    (hk : F.AfterLine k) : (F.key k:ℕ) ∉ F.comparisonSupport i j := by
  simp only [comparisonSupport,mem_union,not_or]
  exact ⟨⟨F.key_private k i (ne_of_lt (hkj.trans hji)),
    F.key_private k j (ne_of_lt hkj)⟩,
    F.after_segment_absent k hk _ _ (F.ordered (hkj.trans hji).le) (F.ordered hkj.le)⟩

lemma own_segment_absent_before (i j : Fin n) (hij : i < j) (hj : F.BeforeLine j) :
    (F.key j:ℕ) ∉ w.segmentSupport (F.witness i).index (F.witness j).index :=
  F.before_segment_absent j hj _ _ (F.ordered hij.le) le_rfl

lemma own_segment_absent_after (i j : Fin n) (hji : j < i) (hj : F.AfterLine j) :
    (F.key j:ℕ) ∉ w.segmentSupport (F.witness i).index (F.witness j).index :=
  F.after_segment_absent j hj _ _ (F.ordered hji.le) le_rfl

end PrivateFamily
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI

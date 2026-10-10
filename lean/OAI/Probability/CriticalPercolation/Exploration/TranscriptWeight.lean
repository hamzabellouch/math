import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.PrefixScoreNonneg
import OAI.Probability.CriticalPercolation.Entropy.FiberValue

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct FiniteEntropy

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def transcriptWeight (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (p : ℝ) (w : E → Prop → ℝ)
    (t : (pair G a b).bare.Leaf) (f : E) : ℝ :=
  fiberValue (pair G a b).bare.run (fun ω => markWeight G order B a b p w ω f) t

noncomputable def transcriptCost (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (p : ℝ) (w : E → Prop → ℝ)
    (t : (pair G a b).bare.Leaf) (f : E) : ℝ :=
  fiberValue (pair G a b).bare.run (fun ω => markCost G order B a b p w ω f) t

lemma transcriptWeight_run (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (p : ℝ) (w : E → Prop → ℝ)
    (ω : E → Bool) (f : E) :
    transcriptWeight G order B a b p w ((pair G a b).bare.run ω) f =
      markWeight G order B a b p w ω f :=
  fiberValue_apply _ _ (fun ω η h => (pair_mark_congr G order B a b hb p w ω η h f).1) ω

lemma transcriptCost_run (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (p : ℝ) (w : E → Prop → ℝ)
    (ω : E → Bool) (f : E) :
    transcriptCost G order B a b p w ((pair G a b).bare.run ω) f =
      markCost G order B a b p w ω f :=
  fiberValue_apply _ _ (fun ω η h => (pair_mark_congr G order B a b hb p w ω η h f).2) ω

noncomputable def contactMeasure (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (p : ℝ) (w : E → Prop → ℝ)
    (z : (pair G a b).bare.Leaf × E) : ℝ :=
  pushMass (pair G a b).bare.run (density (QueryTree.bitWeight p)) z.1 *
    transcriptWeight G order B a b p w z.1 z.2

theorem contactMeasure_bound (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (horder : LazyDFS.GoodDarts G order) (ho : LazyDFS.Exhaustive G order)
    (B : Set V) (a b : V) (hb : b ∈ B) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    (∑ z, contactMeasure G order B a b p w z *
      (1 + transcriptCost G order B a b p w z.1 z.2)) ≤ 4 := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [contactMeasure,mul_assoc]
  simp_rw [sum_pushMass_mul]
  simp_rw [transcriptWeight_run G order B a b hb,transcriptCost_run G order B a b hb]
  rw [Finset.sum_comm]
  simpa only [expect,Finset.mul_sum] using marked_pair_bound G order horder ho B a b hb hp w h0 h1

lemma transcript_nonneg (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (t : (pair G a b).bare.Leaf) (f : E) :
    0 ≤ transcriptWeight G order B a b p w t f ∧
      0 ≤ transcriptCost G order B a b p w t f :=
  ⟨fiberValue_nonneg _ _ (fun ω => (mark_nonneg G order B a b hp w h0 h1 ω f).1) t,
    fiberValue_nonneg _ _ (fun ω => (mark_nonneg G order B a b hp w h0 h1 ω f).2) t⟩

end CriticalPercolation.ExactExposure
end
end

end OAI

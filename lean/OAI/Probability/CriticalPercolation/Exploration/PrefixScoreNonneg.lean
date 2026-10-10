import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.SearchMarkedContactBound
import OAI.Probability.CriticalPercolation.Exploration.ClusterUsers

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

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma prefixScore_nonneg (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) (e : E) :
    0 ≤ T.prefixScore p F w ω e := by
  induction T generalizing used w with
  | done _ => exact le_rfl
  | ask f l r hl hr =>
    rw [prefixScore]
    apply add_nonneg
    · split_ifs
      · have hf0 : w f False ≠ 0 := by rw [(hf f hT.1).1]; linarith [hp.2]
        have hf1 : w f True ≠ 0 := by rw [(hf f hT.1).2]; exact hp.1.ne'
        exact mul_nonneg (sub_nonneg.mpr hp.2.le) (delta_unit w hw hn f hf0 hf1 F hF).1
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact hr _ hT.2.2 _ (pin_normalized w hw f True) (pin_nonneg w hn f True)
          (fresh_pin w p used hf f True)
      · exact hl _ hT.2.1 _ (pin_normalized w hw f False) (pin_nonneg w hn f False)
          (fresh_pin w p used hf f False)
end CriticalPercolation.SearchTree

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree LazyDFS

variable {V E : Type*} [Fintype V] [Fintype E]

lemma markWeight_closedPivot (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (p : ℝ) (w : E → Prop → ℝ)
    (ω : E → Bool) (f : E) (ha : Admissible G B a b ω f) :
    markWeight G order B a b p w ω f =
      (LazyDFS.search G order a B).closedPivotWeight p
        (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w (configuration ω) f := by
  have hc := admissible_closed G B a b hb ω f ha
  obtain ⟨hn,u,v,hf,hu,hv⟩ := ha
  have hp := G.contact_exit_pivot (configuration ω) B a u v f hf hc hn hu ⟨b,hb,hv.symm⟩
  rw [markWeight,ite_eq_left ⟨hn,u,v,hf,hu,hv⟩,closedPivotWeight,ite_eq_left ⟨hc,hp⟩]

lemma mark_nonneg (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (ω : E → Bool) (f : E) :
    0 ≤ markWeight G order B a b p w ω f ∧ 0 ≤ markCost G order B a b p w ω f := by
  have hv : (LazyDFS.search G order a B).Valid ∅ := LazyDFS.compile_valid G order B _ _ _
  have hF : ∀ s t : Set E, s ⊆ t → (∃ v ∈ B, (G.openGraph s).Reachable a v) →
      ∃ v ∈ B, (G.openGraph t).Reachable a v := by
    rintro s t hst ⟨v,hv,hr⟩
    exact ⟨v,hv,hr.mono (G.openGraph_mono hst)⟩
  have hw := homogeneous_normalized w p h0 h1
  have hn : ∀ e b, 0 ≤ w e b := fun e b => (homogeneous_positive w hp h0 h1 e b).le
  have hf : Fresh w p ∅ := fun e _ => ⟨h0 e,h1 e⟩
  unfold markWeight markCost
  split_ifs
  · exact ⟨mul_nonneg hp.1.le (queryDelta_nonneg _ _ hv hp _ hF w hw hn hf _ f),
      prefixScore_nonneg _ _ hv hp _ hF w hw hn hf _ f⟩
  · exact ⟨le_rfl,le_rfl⟩

lemma mark_cost_le_pivotal (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (f : E) :
    markWeight G order B a b p w ω f * (1 + markCost G order B a b p w ω f) ≤
      (LazyDFS.search G order a B).closedPivotWeight p
        (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w (configuration ω) f *
      (1 + (LazyDFS.search G order a B).prefixScore p
        (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w
        (Function.update (configuration ω) f True) f) := by
  by_cases ha : Admissible G B a b ω f
  · rw [markWeight_closedPivot G order B a b hb p w ω f ha,markCost,ite_eq_left ha]
  · rw [markWeight,ite_eq_right ha,zero_mul]
    have hv : (LazyDFS.search G order a B).Valid ∅ := LazyDFS.compile_valid G order B _ _ _
    have hF : ∀ s t : Set E, s ⊆ t → (∃ v ∈ B, (G.openGraph s).Reachable a v) →
        ∃ v ∈ B, (G.openGraph t).Reachable a v := by
      rintro s t hst ⟨v,hv,hr⟩
      exact ⟨v,hv,hr.mono (G.openGraph_mono hst)⟩
    have hw := homogeneous_normalized w p h0 h1
    have hn : ∀ e b, 0 ≤ w e b := fun e b => (homogeneous_positive w hp h0 h1 e b).le
    have hf : Fresh w p ∅ := fun e _ => ⟨h0 e,h1 e⟩
    have hpre := prefixScore_nonneg _ _ hv hp _ hF w hw hn hf
      (Function.update (configuration ω) f True) f
    exact mul_nonneg (closedPivotWeight_nonneg _ _ hv hp _ hF w hw hn hf _ f)
      (by linarith)

lemma expect_configuration (w : E → Prop → ℝ) (f : Set E → ℝ) :
    expect (fun e (b : Bool) => w e (b = true)) (fun ω => f (configuration ω)) =
      expect w f := by
  let e : (E → Bool) ≃ (E → Prop) := Equiv.piCongrRight (fun _ => Equiv.propEquivBool.symm)
  have he (ω : E → Bool) : e ω = configuration ω := rfl
  unfold expect
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  rw [he]
  rfl

theorem marked_pair_bound (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (horder : LazyDFS.GoodDarts G order) (ho : LazyDFS.Exhaustive G order)
    (B : Set V) (a b : V) (hb : b ∈ B) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    expect (QueryTree.bitWeight p) (fun ω => ∑ f,
      markWeight G order B a b p w ω f * (1 + markCost G order B a b p w ω f)) ≤ 4 := by
  have hw : QueryTree.bitWeight p = fun e (b : Bool) => w e (b = true) := by
    funext e b
    cases b <;> simp [QueryTree.bitWeight,h0,h1]
  rw [hw]
  calc
    _ ≤ expect (fun e (b : Bool) => w e (b = true)) (fun ω => ∑ f,
        (LazyDFS.search G order a B).closedPivotWeight p
          (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w (configuration ω) f *
        (1 + (LazyDFS.search G order a B).prefixScore p
          (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w
            (Function.update (configuration ω) f True) f)) := by
      apply expect_mono (fun e b => (homogeneous_positive w hp h0 h1 e (b = true)).le)
      intro ω
      exact Finset.sum_le_sum fun f _ => mark_cost_le_pivotal G order B a b hb hp w h0 h1 ω f
    _ ≤ 4 := by
      let F := fun σ : Set E => ∃ t ∈ B, (G.openGraph σ).Reachable a t
      let T := LazyDFS.search G order a B
      let g := fun σ : Set E => ∑ f, T.closedPivotWeight p F w σ f *
        (1 + T.prefixScore p F w (Function.update σ f True) f)
      change expect (fun e (b : Bool) => w e (b = true)) (fun ω => g (configuration ω)) ≤ 4
      rw [expect_configuration w g]
      exact LazyDFS.search_marked_contact_bound G B order horder ho a hp w h0 h1

end CriticalPercolation.ExactExposure

end
end

end OAI

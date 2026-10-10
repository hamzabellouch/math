import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.SearchContactMoments
import OAI.Probability.CriticalPercolation.Exploration.CompileContactScoreErase
import OAI.Probability.CriticalPercolation.ProductMeasure.ExposureLawSupport

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V] [DecidableEq E]

theorem search_contact_moments_exposure (G : BondGraph V E)
    (order : List (Dart V E)) (ho : ∀ v e z, G.ends e = s(v,z) → (v,e,z) ∈ order)
    (B O : Set V) (a : V) (ha : a ∉ O) (hB : B ⊆ O) (σ : Set E)
    (hσ : ∀ e ∈ G.cutEdges O, ¬σ e) (p : ℝ) (hp : 0 < p ∧ p < 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
    let T := search G order a B
    let v := exposureLaw w (G.incidentEdges O) σ
    expect v (T.contactScore p (G.cutEdges O) F w) = prob w F ∧
    expect v (fun ω => (T.contactScore p (G.cutEdges O) F w ω)^2) ≤ 3 := by
  dsimp only
  let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
  let v := exposureLaw w (G.incidentEdges O) σ
  let v' := forceClosed w (G.cutEdges O)
  have hw := homogeneous_normalized w p h0 h1
  have hv : ∀ e, ∑ b, v e b = 1 := exposureLaw_normalized w _ σ hw
  have hv' : ∀ e, ∑ b, v' e b = 1 := forceClosed_normalized w _ hw
  have hc : ∀ ω, density v ω ≠ 0 → ∀ e ∈ G.cutEdges O, ¬ω e := by
    intro ω hω e he hbit
    have hh := exposureLaw_support w (G.incidentEdges O) σ ω hω e
      (G.cutEdges_subset_incidentEdges O he)
    exact hσ e he (hh ▸ hbit)
  have hc' : ∀ ω, density v' ω ≠ 0 → ∀ e ∈ G.cutEdges O, ¬ω e :=
    fun ω hω => forceClosed_support w _ ω hω
  have heq : ∀ e ∉ G.incidentEdges O, v e = v' e := by
    intro e he
    have he' : e ∉ G.cutEdges O := fun hc => he (G.cutEdges_subset_incidentEdges O hc)
    funext b
    simp [v,v',exposureLaw,forceClosed,he,he']
  have ht := search_contact_moments G order ho O B hB a ha hp w h0 h1
  constructor
  · exact (contact_expect_exterior G order B O a ha p F w v v' hv hv' hc hc' heq id).trans ht.1
  · exact (contact_expect_exterior G order B O a ha p F w v v' hv hv' hc hc' heq
      (fun x => x^2)).le.trans ht.2

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

noncomputable def queryDelta (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E) : ℝ :=
  match T with
  | .done _ => 0
  | .ask f l r => if e = f then delta w F f else
      if ω f then r.queryDelta F (pin w f True) ω e
      else l.queryDelta F (pin w f False) ω e

lemma queryDelta_update (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E) (b : Prop) :
    T.queryDelta F w (Function.update ω e b) e = T.queryDelta F w ω e := by
  induction T generalizing w with
  | done _ => rfl
  | ask f l r hl hr =>
    simp only [queryDelta]
    by_cases he : e = f
    · simp only [ite_eq_left he]
    · have hfe : f ≠ e := Ne.symm he
      simp only [ite_eq_right he]
      erw [Function.update_of_ne hfe]
      split_ifs <;> first | exact hr _ | exact hl _

lemma queryDelta_zero_used (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) (e : E) (he : e ∈ used) :
    T.queryDelta F w ω e = 0 := by
  induction T generalizing used w with
  | done _ => rfl
  | ask f l r hl hr =>
    have hef : e ≠ f := fun h => hT.1 (h ▸ he)
    simp only [queryDelta,ite_eq_right hef]
    split_ifs
    · exact hr _ hT.2.2 _ (Finset.mem_insert_of_mem he)
    · exact hl _ hT.2.1 _ (Finset.mem_insert_of_mem he)

lemma queryDelta_nonneg (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) (e : E) : 0 ≤ T.queryDelta F w ω e := by
  induction T generalizing used w with
  | done _ => exact le_rfl
  | ask f l r hl hr =>
    have hf0 : w f False ≠ 0 := by rw [(hf f hT.1).1]; linarith [hp.2]
    have hf1 : w f True ≠ 0 := by rw [(hf f hT.1).2]; exact hp.1.ne'
    simp only [queryDelta]
    split_ifs
    · exact (delta_unit w hw hn f hf0 hf1 F hF).1
    · exact hr _ hT.2.2 _ (pin_normalized w hw f True) (pin_nonneg w hn f True)
        (fresh_pin w p used hf f True)
    · exact hl _ hT.2.1 _ (pin_normalized w hw f False) (pin_nonneg w hn f False)
        (fresh_pin w p used hf f False)

theorem score_eq_queryDelta_sum (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) :
    T.score p F w ω = ∑ e, if openPivot F e ω then (1-p)*T.queryDelta F w ω e else 0 := by
  induction T generalizing used w with
  | done _ => simp [score,queryDelta]
  | ask f l r hl hr =>
    have hsum (T' : SearchTree E R) (w' : E → Prop → ℝ) (hT' : T'.Valid (insert f used)) :
        (∑ e, if openPivot F e ω then
          (1-p)*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) =
        (if openPivot F f ω then (1-p)*delta w F f else 0) +
          ∑ e, if openPivot F e ω then (1-p)*T'.queryDelta F w' ω e else 0 := by
      have hz := queryDelta_zero_used T' _ hT' F w' ω f (Finset.mem_insert_self _ _)
      have heq (e : E) : (if openPivot F e ω then
          (1-p)*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) =
          (if e = f then (if openPivot F f ω then (1-p)*delta w F f else 0) else 0) +
          (if openPivot F e ω then (1-p)*T'.queryDelta F w' ω e else 0) := by
        by_cases he : e = f
        · subst e; rw [hz]; simp
        · simp only [ite_eq_right he,zero_add]
      simp only [heq,Finset.sum_add_distrib]
      simp
    rw [score]
    by_cases hf : ω f
    · simp only [ite_eq_left hf,queryDelta]
      rw [hr _ hT.2.2 (pin w f True),← hsum r (pin w f True) hT.2.2]
    · simp only [ite_eq_right hf,queryDelta]
      rw [hl _ hT.2.1 (pin w f False),← hsum l (pin w f False) hT.2.1]

lemma score_nonneg (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) : 0 ≤ T.score p F w ω := by
  rw [score_eq_queryDelta_sum T used hT]
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact mul_nonneg (sub_nonneg.mpr hp.2.le) (queryDelta_nonneg T used hT hp F hF w hw hn hf ω e)
  · exact le_rfl

end CriticalPercolation.SearchTree

end
end

end OAI

import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.Initial
import OAI.Probability.CriticalPercolation.Exploration.ReachableMemPhaseClosed
import OAI.Probability.CriticalPercolation.Exploration.ListScore
import OAI.Probability.CriticalPercolation.Exploration.ScoreCongrSupport
import OAI.Probability.CriticalPercolation.GraphGeometry.Connects
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphInsert

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V]

theorem actual_pivot_no_older_reads (G : BondGraph V E)
    (order : List (Dart V E)) (ho : Exhaustive G order) (B : Set V)
    (fuel : ℕ) (st : State V E) (older : List (Dart V E)) (ω : E → Bool)
    (w a z : V) (f : E) (ha : a ∈ st.reached) (he : G.ends f = s(a,z))
    (hf : ω f = true) (hc : ReadConsistent G st ω)
    (hr : rank order (st.opened f z) (push G order z) ≤ fuel)
    (hA : ∀ u ∈ st.reached, (G.openGraph {e | e ≠ f ∧ ω e = true}).Reachable w u)
    (hopen : ∃ t ∈ B, (G.openGraph {e | ω e = true}).Reachable w t)
    (hclosed : ¬∃ t ∈ B, (G.openGraph {e | Function.update ω f false e = true}).Reachable w t) :
    (compile G order B fuel (st.opened f z) (push G order z++older)).reads ω =
      (compile G order B fuel (st.opened f z) (push G order z)).reads ω := by
  have hopen' := hopen
  rw [G.openGraph_delete_sup ω f a z hf he] at hopen'
  rw [← G.openGraph_delete_eq_update] at hclosed
  obtain ⟨ht,havoid⟩ := Wiring.pivot_component_avoids
    (G.openGraph {e | e ≠ f ∧ ω e = true}) (st.reached : Set V) B w a z ha hA hopen' hclosed
  apply phase_no_older_reads G (st.reached : Set V) order ho B fuel (st.opened f z)
    (push G order z) older ω (opened_phaseFrontier G order ho st f z)
    (readConsistent_opened G st ω hc ha he) hr
    (G.openGraph {e | e ≠ f ∧ ω e = true})
    (SimpleGraph.fromEdgeSet_mono (Set.image_mono (fun _ h => h.2))) z
    (Finset.mem_insert_self _ _) havoid ht

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

def PrefixState (G : BondGraph V E) (a : V) (st : State V E)
    (w : E → Prop → ℝ) : Prop :=
  a ∈ st.reached ∧ ∀ ω : Set E, density w ω ≠ 0 →
    (∀ v ∈ st.reached, (G.openGraph {e | e ∈ st.read ∧ e ∈ ω}).Reachable a v) ∧
    ReadConsistent G st (fun e => decide (ω e))

omit [DecidableEq V] [DecidableEq E] in
lemma prefixState_initial (G : BondGraph V E) (a : V) (w : E → Prop → ℝ) :
    PrefixState G a (initial a) w := by
  refine ⟨Finset.mem_singleton_self _,?_⟩
  intro ω _
  constructor
  · intro v hv
    have hv' : v = a := Finset.mem_singleton.mp hv
    subst v
    exact .refl _
  · intro e he
    exact (Finset.notMem_empty e he).elim

omit [DecidableEq V] in
lemma prefixState_closed (G : BondGraph V E) (a : V) (st : State V E)
    (w : E → Prop → ℝ) (hs : PrefixState G a st w) (e : E) (h0 : w e False ≠ 0) :
    PrefixState G a (st.closed e) (pin w e False) := by
  refine ⟨hs.1,?_⟩
  intro ω hω
  have hold := hs.2 ω (density_pin_old_support w e False ω h0 hω)
  constructor
  · intro v hv
    apply (hold.1 v hv).mono
    exact G.openGraph_mono (fun j hj => ⟨Finset.mem_insert_of_mem hj.1,hj.2⟩)
  · apply readConsistent_closed G st (fun j => decide (ω j)) hold.2
    have hh := density_pin_support w e False ω hω
    simp only [hh,decide_false]

lemma prefixState_opened (G : BondGraph V E) (a : V) (st : State V E)
    (w : E → Prop → ℝ) (hs : PrefixState G a st w) (e : E) (v z : V)
    (hv : v ∈ st.reached) (he : G.ends e = s(v,z)) (h1 : w e True ≠ 0) :
    PrefixState G a (st.opened e z) (pin w e True) := by
  refine ⟨Finset.mem_insert_of_mem hs.1,?_⟩
  intro ω hω
  have hold := hs.2 ω (density_pin_old_support w e True ω h1 hω)
  have hle : G.openGraph {j | j ∈ st.read ∧ j ∈ ω} ≤
      G.openGraph {j | j ∈ (st.opened e z).read ∧ j ∈ ω} :=
    G.openGraph_mono (fun j hj => ⟨Finset.mem_insert_of_mem hj.1,hj.2⟩)
  constructor
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · apply ((hold.1 v hv).mono hle).trans
      apply prop_openEdge_reachable G {j | j ∈ insert e st.read ∧ j ∈ ω} _ he
      exact ⟨Finset.mem_insert_self _ _,of_eq_true (density_pin_support w e True ω hω)⟩
    · exact (hold.1 u hu).mono hle
  · exact readConsistent_opened G st (fun j => decide (ω j)) hold.2 hv he

omit [DecidableEq V] [DecidableEq E] in
lemma prefixState_deleted (G : BondGraph V E) (a : V) (st : State V E)
    (w : E → Prop → ℝ) (hs : PrefixState G a st w) (f : E) (hf : f ∉ st.read)
    (ω : Set E) (hω : density w ω ≠ 0) :
    ∀ v ∈ st.reached, ((G.eraseBond f a).openGraph ω).Reachable a v := by
  intro v hv
  exact ((hs.2 ω hω).1 v hv).mono (G.knownGraph_le_eraseBond st.read f a ω hf)

variable [Fintype V]

theorem future_pair_bound (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (a t v z : V) (f : E)
    (st : State V E) (older : List (Dart V E)) (fuel : ℕ)
    (hv : v ∈ st.reached) (hz : z ∉ st.reached) (ht : t ∉ st.reached) (hzt : z ≠ t)
    (hf : f ∉ st.read) (he : G.ends f = s(v,z))
    (hr : rank order (st.opened f z) (push G order z) ≤ fuel)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (fresh : Fresh w p st.read) (hs : PrefixState G a st w) :
    expect (pin w f True) (fun ω => if openPivot (G.connects a t) f ω then
      (compile G order {t} fuel (st.opened f z) (push G order z++older)).score p
        (G.connects a t) (pin w f True) ω else 0) ≤ delta w (G.connects a t) f := by
  have hb := fresh f hf
  have h0 : w f False ≠ 0 := by rw [hb.1]; exact (sub_pos.mpr hp.2).ne'
  have h1 : w f True ≠ 0 := by rw [hb.2]; exact hp.1.ne'
  have haz : a ≠ z := fun h => hz (h ▸ hs.1)
  have hat : a ≠ t := fun h => ht (h ▸ hs.1)
  have hA : ∀ ω : Set E, density w ω ≠ 0 →
      ∀ u ∈ st.reached, ((G.eraseBond f a).openGraph ω).Reachable a u :=
    prefixState_deleted G a st w hs f hf
  have hd := G.delta_eq_deleted_joined w hw f h0 h1 a v z t he
    (fun ω hω => hA ω (density_pin_old_support w f False ω h0 hω) v hv)
  rw [hd]
  have hphase := young_phase_score_bound G order {t} f a z t haz hat hzt hp fuel (st.opened f z)
    (Finset.mem_insert_self _ _) (pin w f True) (pin_normalized w hw f True)
    (pin_nonneg w hn f True) (fresh_pin w p st.read fresh f True)
  apply le_trans (le_of_eq ?_) hphase
  apply expect_congr_support
  intro ω hω
  change Set E at ω
  have hωold := density_pin_old_support w f True ω h1 hω
  have hopenf : ω f := of_eq_true (density_pin_support w f True ω hω)
  have hP := G.pivot_eq_deleted_joined f a v z t ω hopenf he (hA ω hωold v hv)
  erw [hP]
  by_cases hR : (G.eraseBond f a).joinedPair a z t ω
  · rw [ite_eq_left hR,ite_eq_left hR]
    have hactual := hP.mpr hR
    have hconn : ∀ η : Set E, density (pin w f True) η ≠ 0 →
        (G.connects a t η ↔ (G.eraseBond f a).wiredEvent a z t η) := by
      intro η hη
      exact G.connects_eq_wired_deleted f a v z t η
        (of_eq_true (density_pin_support w f True η hη)) he
        (hA η (density_pin_old_support w f True η h1 hη) v hv)
    apply Eq.trans (SearchTree.score_eq_of_reads_eq _ _ p (G.connects a t) (pin w f True) ω ?_)
      (SearchTree.score_congr_support _ (st.opened f z).read
        (compile_valid G order {t} fuel (st.opened f z) (push G order z)) hp
        (pin w f True) (fresh_pin w p st.read fresh f True) _ _ hconn ω hω)
    apply actual_pivot_no_older_reads G order ho {t} fuel st older (fun e => decide (ω e))
      a v z f hv he (by simp [hopenf]) (hs.2 ω hωold).2 hr
    · intro u hu
      have hh := hA ω hωold u hu
      erw [G.eraseBond_openGraph] at hh
      convert hh using 1
      simp only [decide_eq_true_eq]
      rfl
    · refine ⟨t,Set.mem_singleton _,?_⟩
      convert hactual.2.1 using 1
      simp only [BondGraph.connects,decide_eq_true_eq]
      rfl
    · rintro ⟨u,hu,hau⟩
      have hu' : u = t := Set.mem_singleton_iff.mp hu
      subst u
      apply hactual.2.2
      have hsets : {e | Function.update (fun j => decide (ω j)) f false e = true} =
          (Function.update ω f False : Set E) := by
        ext e
        change (Function.update (fun j => decide (ω j)) f false e = true) ↔ Function.update ω f False e
        by_cases hf' : e = f
        · subst e
          erw [Function.update_self,Function.update_self]
          simp
        · erw [Function.update_of_ne hf',Function.update_of_ne hf']
          simp only [decide_eq_true_eq]
      erw [hsets] at hau
      unfold BondGraph.connects
      convert hau using 1
      congr 1
      funext e
      dsimp only [Function.update]
      split_ifs <;> rfl
  · rw [ite_eq_right hR,ite_eq_right hR]

end CriticalPercolation.LazyDFS

end
end

end OAI

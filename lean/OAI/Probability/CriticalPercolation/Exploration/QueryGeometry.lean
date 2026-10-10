import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.SequentialExposure

namespace OAI

section
section
namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

lemma compile_queryDelta_incident (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) (a : V) (e : E)
    (hst : ∀ v ∈ st.reached, (G.openGraph ω).Reachable a v)
    (hq : (compile G order B fuel st stack).queryDelta F w ω e ≠ 0) :
    ∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v := by
  induction fuel generalizing st stack w with
  | zero => exact (hq rfl).elim
  | succ n ih =>
    rw [compile.eq_def] at hq
    dsimp only at hq
    split_ifs at hq with hh
    · exact (hq rfl).elim
    · cases stack with
      | nil => exact (hq rfl).elim
      | cons d rest =>
        dsimp only at hq
        split_ifs at hq with hd
        · exact ih st rest w hst hq
        · have htail : d.1 ∈ st.reached := by
            by_contra ht
            exact hd (Or.inr (Or.inr (Or.inl ht)))
          have he : G.ends d.2.1 = s(d.1,d.2.2) := by
            by_contra ht
            exact hd (Or.inr (Or.inr (Or.inr ht)))
          by_cases hef : e=d.2.1
          · subst e
            exact ⟨d.1,by simp [he],hst d.1 htail⟩
          · simp only [queryDelta,ite_eq_right hef] at hq
            by_cases hopen : ω d.2.1
            · rw [ite_eq_left hopen] at hq
              apply ih _ _ _ (fun v hv => ?_) hq
              rcases Finset.mem_insert.mp hv with rfl|hv
              · exact (hst d.1 htail).trans (prop_openEdge_reachable G ω hopen he)
              · exact hst v hv
            · rw [ite_eq_right hopen] at hq
              exact ih (st.closed d.2.1) rest (pin w d.2.1 False) (fun v hv => hst v hv) hq

lemma search_queryDelta_incident [Fintype V] (G : BondGraph V E)
    (order : List (Dart V E)) (B : Set V) (a : V) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E)
    (hq : (search G order a B).queryDelta F w ω e ≠ 0) :
    ∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v := by
  apply compile_queryDelta_incident G order B _ _ _ F w ω a e _ hq
  intro v hv
  have he : v=a := Finset.mem_singleton.mp hv
  subst v
  exact .refl _

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

theorem kernel_contact_geometry (order : List (LazyDFS.Dart V E))
    (S : Set V) (a : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (e : E)
    (hk : G.contactKernel order S a p w (G.clusterObject ω S) ω (some e) ≠ 0) :
    a ∉ (G.clusterObject ω S).1 ∧ ¬ω e ∧ ∃ u v,
      G.ends e=s(u,v) ∧ (G.openGraph ω).Reachable a u ∧ v ∈ (G.clusterObject ω S).1 := by
  have ha : a ∉ (G.clusterObject ω S).1 := by
    intro ha
    simp only [contactKernel,ite_eq_left ha,Option.some_ne_none,ite_false] at hk
    exact hk rfl
  have he : e ∈ G.cutEdges (G.clusterObject ω S).1 := by
    by_contra he
    simp only [contactKernel,ite_eq_right ha,contactWeight,ite_eq_right he,zero_div] at hk
    exact hk rfl
  have hc : ¬ω e := fun hoe => G.clusterObject_cut_closed ω S e he
    ⟨hoe,G.cutEdges_subset_incidentEdges _ he⟩
  obtain ⟨u,v,heq,hu,hv⟩ := he
  have hq : (LazyDFS.search G order a S).queryDelta
      (fun σ => ∃ b ∈ S, (G.openGraph σ).Reachable a b) w ω e ≠ 0 := by
    intro hq
    simp only [contactKernel,ite_eq_right ha,contactWeight,hq,mul_zero,ite_self,zero_div] at hk
    exact hk rfl
  obtain ⟨z,hz,hr⟩ := LazyDFS.search_queryDelta_incident G order S a _ w ω e hq
  have hzu : z=u := by
    rw [heq,Sym2.mem_iff] at hz
    rcases hz with rfl|rfl
    · rfl
    · obtain ⟨b,hb,hbv⟩ := hv
      exact (ha ⟨b,hb,hbv.trans hr.symm⟩).elim
  exact ⟨ha,hc,u,v,heq,hzu ▸ hr,hv⟩

end CriticalPercolation.BinaryLaw
end
end

end OAI

import Mathlib
import OAI.Probability.CriticalPercolation.Entropy.ReverseGuess
import OAI.Probability.CriticalPercolation.Gluing.ContactExitPivot

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

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

theorem compile_contact_prefix_congr (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (p : ℝ) (F : Set E → Prop) (w : E → Prop → ℝ) (ω η : Set E) (a : V) (f : E)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g))
    (hpiv : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) →
      (openPivot F g (Function.update ω f True) ↔ openPivot F g (Function.update η f True)))
    (hst : ∀ v ∈ st.reached, (G.openGraph ω).Reachable a v) :
    (compile G order B fuel st stack).queryDelta F w (Function.update ω f True) f =
      (compile G order B fuel st stack).queryDelta F w (Function.update η f True) f ∧
    (compile G order B fuel st stack).prefixScore p F w (Function.update ω f True) f =
      (compile G order B fuel st stack).prefixScore p F w (Function.update η f True) f := by
  induction fuel generalizing st stack w with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · exact ⟨rfl,rfl⟩
    · cases stack with
      | nil => exact ⟨rfl,rfl⟩
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest w hst
        · have htail : d.1 ∈ st.reached := by
            by_contra ht; exact hd (Or.inr (Or.inr (Or.inl ht)))
          have he : G.ends d.2.1 = s(d.1,d.2.2) := by
            by_contra ht; exact hd (Or.inr (Or.inr (Or.inr ht)))
          have hinc : ∃ r ∈ G.ends d.2.1, (G.openGraph ω).Reachable a r :=
            ⟨d.1,by simp [he],hst d.1 htail⟩
          have hp := propext (hpiv d.2.1 hinc)
          simp only [queryDelta,prefixScore,hp]
          by_cases hfe : f = d.2.1
          · simp only [ite_eq_left hfe, and_self]
          · simp only [ite_eq_right hfe]
            have hdf : d.2.1 ≠ f := Ne.symm hfe
            erw [Function.update_of_ne hdf,Function.update_of_ne hdf]
            have hb := propext (h d.2.1 hinc)
            rw [← hb]
            by_cases hopen : ω d.2.1
            · simp only [ite_eq_left hopen]
              have hs' : ∀ v ∈ (st.opened d.2.1 d.2.2).reached,
                  (G.openGraph ω).Reachable a v := by
                intro v hv
                rcases Finset.mem_insert.mp hv with rfl | hv
                · exact (hst d.1 htail).trans (prop_openEdge_reachable G ω hopen he)
                · exact hst v hv
              obtain ⟨hq,hs⟩ := ih (st.opened d.2.1 d.2.2) (push G order d.2.2 ++ rest)
                (pin w d.2.1 True) hs'
              exact ⟨hq,congrArg (_ + ·) hs⟩
            · simp only [ite_eq_right hopen]
              obtain ⟨hq,hs⟩ := ih (st.closed d.2.1) rest (pin w d.2.1 False) hst
              exact ⟨hq,congrArg (_ + ·) hs⟩

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V] [DecidableEq E]

theorem search_contact_reconstruction (G : BondGraph V E) (order : List (Dart V E))
    (ω η : Set E) (B : Set V) (a u v : V) (f : E)
    (hf : G.ends f = s(u,v)) (hclosed : ¬ω f)
    (hn : ¬∃ b ∈ B, (G.openGraph ω).Reachable a b)
    (hau : (G.openGraph ω).Reachable a u)
    (hv : ∃ b ∈ B, (G.openGraph ω).Reachable v b)
    (hv' : ∃ b ∈ B, (G.openGraph η).Reachable v b)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g))
    (p : ℝ) (w : E → Prop → ℝ) (s : ℝ) :
    let F := fun σ : Set E => ∃ b ∈ B, (G.openGraph σ).Reachable a b
    let T := search G order a B
    T.queryDelta F w (Function.update ω f True) f =
      T.queryDelta F w (Function.update η f True) f ∧
    T.prefixScore p F w (Function.update ω f True) f =
      T.prefixScore p F w (Function.update η f True) f ∧
    T.reverseGuess p F w (Function.update ω f True) s f =
      T.reverseGuess p F w (Function.update η f True) s f := by
  let F := fun σ : Set E => ∃ b ∈ B, (G.openGraph σ).Reachable a b
  have hup (σ : Set E) :
      @Function.update E (fun _ => Prop) (fun a b => Classical.propDecidable (a=b)) σ f True =
        Function.update σ f True := by
    exact congrArg (fun d' : DecidableEq E =>
      @Function.update E (fun _ => Prop) d' σ f True) (Subsingleton.elim _ _)
  have hpiv : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) →
      (openPivot F g (Function.update ω f True) ↔
        openPivot F g (Function.update η f True)) := by
    intro g hg
    simpa only [hup] using
      G.contact_pivot_incidence_congr ω η B a u v f g hf hclosed hn hau hv hv' h hg
  have hst : ∀ t ∈ (initial (E := E) a).reached, (G.openGraph ω).Reachable a t := by
    intro t ht
    have hta : t = a := Finset.mem_singleton.mp ht
    subst t
    exact .refl _
  obtain ⟨hd,hs⟩ := compile_contact_prefix_congr G order B _ _ _ p F w ω η a f h hpiv hst
  refine ⟨hd,hs,?_⟩
  change (search G order a B).reverseGuess p F w (Function.update ω f True) s f =
    (search G order a B).reverseGuess p F w (Function.update η f True) s f
  dsimp only [SearchTree.reverseGuess, search]
  erw [hd,hs,propext (hpiv f ⟨u,by simp [hf],hau⟩)]

end CriticalPercolation.LazyDFS

open scoped Classical
open Real

end
end

end OAI

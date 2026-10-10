import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.ProductMeasure.Delta
import OAI.Probability.CriticalPercolation.Exploration.ReachableIncidenceImp
import OAI.Probability.CriticalPercolation.GraphGeometry.ReachableReplaceTail
import OAI.Probability.CriticalPercolation.Gluing.ContactPivot

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*}

lemma contact_exit_pivot (G : BondGraph V E) (ω : Set E) (B : Set V)
    (a u v : V) (f : E) (hf : G.ends f = s(u,v)) (hclosed : ¬ω f)
    (hn : ¬∃ b ∈ B, (G.openGraph ω).Reachable a b)
    (hau : (G.openGraph ω).Reachable a u)
    (hv : ∃ b ∈ B, (G.openGraph ω).Reachable v b) :
    openPivot (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b)
      f (Function.update ω f True) := by
  apply (openPivot_force_true _ _ _).mpr
  constructor
  · apply (G.target_after_open_iff ω B a u v f hf hn hv ?_).mpr hau
    intro hav
    obtain ⟨b,hb,hvb⟩ := hv
    exact hn ⟨b,hb,hav.trans hvb⟩
  · rw [G.openGraph_force_false_of_closed ω f hclosed]
    exact hn

theorem contact_pivot_incidence_congr (G : BondGraph V E) (ω η : Set E) (B : Set V)
    (a u v : V) (f e : E) (hf : G.ends f = s(u,v)) (hclosed : ¬ω f)
    (hn : ¬∃ b ∈ B, (G.openGraph ω).Reachable a b)
    (hau : (G.openGraph ω).Reachable a u)
    (hv : ∃ b ∈ B, (G.openGraph ω).Reachable v b)
    (hv' : ∃ b ∈ B, (G.openGraph η).Reachable v b)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g))
    (he : ∃ r ∈ G.ends e, (G.openGraph ω).Reachable a r) :
    openPivot (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) e (Function.update ω f True) ↔
      openPivot (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) e (Function.update η f True) := by
  have hr := G.reachable_incidence_congr ω η a h
  have hn' : ¬∃ b ∈ B, (G.openGraph η).Reachable a b := by
    rintro ⟨b,hb,hab⟩; exact hn ⟨b,hb,(hr b).mpr hab⟩
  have hau' := (hr u).mp hau
  by_cases hef : e = f
  · subst e
    have hclosed' : ¬η f := fun he => hclosed ((h f ⟨u,by simp [hf],hau⟩).mpr he)
    exact iff_of_true (G.contact_exit_pivot ω B a u v f hf hclosed hn hau hv)
      (G.contact_exit_pivot η B a u v f hf hclosed' hn' hau' hv')
  · have he' : ∃ r ∈ G.ends e, (G.openGraph η).Reachable a r := by
      obtain ⟨r,her,har⟩ := he; exact ⟨r,her,(hr r).mp har⟩
    rw [G.contact_pivot_iff ω B a u v f e hf hef hn hau hv he,
      G.contact_pivot_iff η B a u v f e hf hef hn' hau' hv' he',h e he,
      G.reachable_delete_incidence_congr ω η a h e u]

end CriticalPercolation.BondGraph

end
end

end OAI

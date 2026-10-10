import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.Delta
import OAI.Probability.CriticalPercolation.GraphGeometry.ForceFalseSubset

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

theorem contact_pivot_iff (G : BondGraph V E) (ω : Set E) (B : Set V)
    (a u v : V) (f e : E) (hf : G.ends f = s(u,v)) (hef : e ≠ f)
    (hn : ¬∃ b ∈ B, (G.openGraph ω).Reachable a b)
    (hau : (G.openGraph ω).Reachable a u)
    (hv : ∃ b ∈ B, (G.openGraph ω).Reachable v b)
    (he : ∃ r ∈ G.ends e, (G.openGraph ω).Reachable a r) :
    openPivot (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b)
      e (Function.update ω f True) ↔
      ω e ∧ ¬(G.openGraph (Function.update ω e False)).Reachable a u := by
  let F := fun σ : Set E => ∃ b ∈ B, (G.openGraph σ).Reachable a b
  have hav : ¬(G.openGraph ω).Reachable a v := by
    intro h
    obtain ⟨b,hb,hvb⟩ := hv
    exact hn ⟨b,hb,h.trans hvb⟩
  have hopen : F (Function.update ω f True) :=
    (G.target_after_open_iff ω B a u v f hf hn hv hav).2 hau
  have hmon : G.openGraph (Function.update ω e False) ≤ G.openGraph ω :=
    SimpleGraph.fromEdgeSet_mono (Set.image_mono (force_false_subset ω e))
  have hn' : ¬∃ b ∈ B, (G.openGraph (Function.update ω e False)).Reachable a b := by
    rintro ⟨b,hb,h⟩
    exact hn ⟨b,hb,h.mono hmon⟩
  have hav' : ¬(G.openGraph (Function.update ω e False)).Reachable a v :=
    fun h => hav (h.mono hmon)
  have hv' : ∃ b ∈ B, (G.openGraph (Function.update ω e False)).Reachable v b := by
    obtain ⟨b,hb,hvb⟩ := hv
    obtain ⟨r,hr,har⟩ := he
    refine ⟨b,hb,G.reachable_force_false_of_not_reachable ω e r hr ?_ hvb⟩
    intro hvr
    exact hav (har.trans hvr.symm)
  have hcomm : Function.update (Function.update ω f True) e False =
      Function.update (Function.update ω e False) f True := by
    funext g
    by_cases hge : g = e
    · subst g; erw [Function.update_self,Function.update_of_ne hef,Function.update_self]
    · by_cases hgf : g = f
      · subst g; erw [Function.update_of_ne (Ne.symm hef),Function.update_self,Function.update_self]
      · erw [Function.update_of_ne hge,Function.update_of_ne hgf,
          Function.update_of_ne hgf,Function.update_of_ne hge]
  have hdelete : F (Function.update (Function.update ω f True) e False) ↔
      (G.openGraph (Function.update ω e False)).Reachable a u := by
    rw [hcomm]
    exact G.target_after_open_iff _ B a u v f hf hn' hv' hav'
  change Function.update ω f True e ∧ F (Function.update ω f True) ∧
      ¬F (Function.update (Function.update ω f True) e False) ↔ _
  erw [Function.update_of_ne hef,hdelete]
  exact and_congr_right (fun _ => and_iff_right hopen)

end CriticalPercolation.BondGraph

end
end

end OAI

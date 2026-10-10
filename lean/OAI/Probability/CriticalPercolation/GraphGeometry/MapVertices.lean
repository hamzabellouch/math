import Mathlib
import OAI.Probability.CriticalPercolation.Model

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E U : Type*} (G : BondGraph V E)

def mapVertices (f : V → U) : BondGraph U E := ⟨Sym2.map f ∘ G.ends⟩

lemma mapVertices_adj (f : V → U) (ω : Set E) (x y : U) :
    ((G.mapVertices f).openGraph ω).Adj x y ↔
      ∃ a b, (G.openGraph ω).Adj a b ∧ f a = x ∧ f b = y ∧ x ≠ y := by
  constructor
  · rintro ⟨⟨e,he,hends⟩,hne⟩
    obtain ⟨a,b,hab⟩ : ∃ a b, G.ends e = s(a,b) :=
      Sym2.exists.mp ⟨G.ends e,rfl⟩
    change Sym2.map f (G.ends e) = s(x,y) at hends
    rw [hab,Sym2.map_mk] at hends
    rcases Sym2.eq_iff.mp hends with ⟨hx,hy⟩ | ⟨hy,hx⟩
    · refine ⟨a,b,?_,hx,hy,hne⟩
      exact ⟨⟨e,he,hab⟩,fun hab' => hne (hx.symm.trans ((congrArg f hab').trans hy))⟩
    · refine ⟨b,a,?_,hx,hy,hne⟩
      exact ⟨⟨e,he,hab.trans Sym2.eq_swap⟩,fun hab' => hne (hx.symm.trans ((congrArg f hab').trans hy))⟩
  · rintro ⟨a,b,⟨⟨e,he,hab⟩,_⟩,hx,hy,hne⟩
    refine ⟨⟨e,he,?_⟩,hne⟩
    change Sym2.map f (G.ends e) = s(x,y)
    rw [hab,Sym2.map_mk,hx,hy]

lemma mapVertices_reachable (f : V → U) (ω : Set E) {a b : V}
    (hab : (G.openGraph ω).Reachable a b) :
    ((G.mapVertices f).openGraph ω).Reachable (f a) (f b) := by
  have hr := ((G.openGraph ω).reachable_iff_reflTransGen a b).mp hab
  clear hab
  induction hr with
  | refl => exact .refl _
  | @tail b c _ hbc ih =>
    apply ih.trans
    by_cases h : f b = f c
    · rw [h]
    · exact ((G.mapVertices_adj f ω _ _).mpr ⟨b,c,hbc,rfl,rfl,h⟩).reachable

open scoped Classical

noncomputable def collapseTarget (B : Set V) (v : V) : Option V :=
  if v ∈ B then none else some v
noncomputable def wireTargets (B : Set V) : BondGraph (Option V) E :=
  G.mapVertices (collapseTarget B)

omit G in
lemma collapseTarget_eq_none (B : Set V) (v : V) : collapseTarget B v = none ↔ v ∈ B := by
  by_cases h : v ∈ B <;> simp [collapseTarget,h]

omit G in
lemma collapseTarget_injective_off (B : Set V) {v u : V} (hu : u ∉ B)
    (h : collapseTarget B v = collapseTarget B u) : v = u := by
  by_cases hv : v ∈ B
  · simp [collapseTarget,hv,hu] at h
  · simpa only [collapseTarget,ite_eq_right hv,ite_eq_right hu,Option.some.injEq] using h

theorem wireTargets_connection (B : Set V) (ω : Set E) (a : V) :
    ((G.wireTargets B).openGraph ω).Reachable (collapseTarget B a) none ↔
      ∃ b ∈ B, (G.openGraph ω).Reachable a b := by
  constructor
  · intro hr
    by_cases ha : a ∈ B
    · exact ⟨a,ha,.refl _⟩
    have hg := (((G.wireTargets B).openGraph ω).reachable_iff_reflTransGen _ _).mp hr.symm
    have hreach : ∀ {y : Option V},
        Relation.ReflTransGen ((G.wireTargets B).openGraph ω).Adj none y →
        ∀ v, collapseTarget B v = y → v ∉ B → ∃ b ∈ B, (G.openGraph ω).Reachable v b := by
      intro y hpath
      induction hpath with
      | refl =>
        intro v hv hn
        exact (hn ((collapseTarget_eq_none B v).mp hv)).elim
      | @tail y z _ hyz ih =>
        intro v hv hn
        obtain ⟨u,u',huu',hu,hu',_⟩ := (G.mapVertices_adj (collapseTarget B) ω y z).mp hyz
        have hu'v : u' = v := collapseTarget_injective_off B hn (hu'.trans hv.symm)
        subst u'
        by_cases huB : u ∈ B
        · exact ⟨u,huB,huu'.symm.reachable⟩
        · obtain ⟨b,hb,hub⟩ := ih u hu huB
          exact ⟨b,hb,huu'.symm.reachable.trans hub⟩
    exact hreach hg a rfl ha
  · rintro ⟨b,hb,hab⟩
    have hh := G.mapVertices_reachable (collapseTarget B) ω hab
    rw [(collapseTarget_eq_none B b).mpr hb] at hh
    exact hh

end CriticalPercolation.BondGraph

end
end

end OAI

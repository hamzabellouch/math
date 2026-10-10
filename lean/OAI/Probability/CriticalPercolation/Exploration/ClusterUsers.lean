import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.CompileContactPrefixCongr
import OAI.Probability.CriticalPercolation.Exploration.GlobalNode
import OAI.Probability.CriticalPercolation.Exploration.Initial2

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

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

theorem pair_transcript_incidence (G : BondGraph V E) (a b : V) (ω η : E → Bool)
    (h : (pair G a b).bare.run ω = (pair G a b).bare.run η)
    (e : E) (he : ∃ v ∈ G.ends e, (G.openGraph {e | ω e = true}).Reachable a v ∨
      (G.openGraph {e | ω e = true}).Reachable b v) : ω e = η e :=
  (SearchTree.bare_run_eq _ ω η h).2 e ((pair_reads G a b ω e).mpr he)

end CriticalPercolation.ExactExposure

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteEntropy FiniteProduct

variable {V E I : Type*} [Fintype E] [Fintype I]

noncomputable def clusterUsers (G : BondGraph V E) (a b : I → V) (ω : E → Bool)
    (v : V) : Finset I :=
  Finset.univ.filter (fun i => (G.openGraph {e | ω e = true}).Reachable (a i) v ∨
    (G.openGraph {e | ω e = true}).Reachable (b i) v)

lemma pair_users (G : BondGraph V E) (a b : I → V) (ω : E → Bool) (e : E)
    (u v : V) (he : G.ends e = s(u,v)) :
    OrderedQuery.users (fun i => (pair G (a i) (b i)).bare) ω e =
      clusterUsers G a b ω u ∪ clusterUsers G a b ω v := by
  ext i
  simp only [OrderedQuery.mem_users,SearchTree.bare_reads,pair_reads,he,Sym2.mem_iff,
    clusterUsers,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨x,hx,hr⟩
    rcases hx with rfl | rfl
    · exact Or.inl hr
    · exact Or.inr hr
  · rintro (h | h)
    · exact ⟨u,Or.inl rfl,h⟩
    · exact ⟨v,Or.inr rfl,h⟩

lemma pair_overlap_four (G : BondGraph V E) (a b : I → V) (ω : E → Bool)
    (h : ∀ v, (clusterUsers G a b ω v).card ≤ 2) (e : E) :
    (OrderedQuery.users (fun i => (pair G (a i) (b i)).bare) ω e).card ≤ 4 := by
  obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective (G.ends e)
  have he' : G.ends e = s(u,v) := he.symm
  rw [pair_users G a b ω e u v he']
  exact (Finset.card_union_le _ _).trans (by have := h u; have := h v; omega)

theorem pair_entropy {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (G : BondGraph V E)
    (a b : I → V) (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (hm : ∑ ω, P ω = 1)
    (hc : ∀ ω, 0 < P ω → ∀ v, (clusterUsers G a b ω v).card ≤ 2) :
    (∑ i, divergence (pushMass (pair G (a i) (b i)).bare.run P)
      ((pair G (a i) (b i)).bare.reference p)) ≤
      16/(2*p*(1-p)) * divergence P (density (QueryTree.bitWeight p)) := by
  have ht (i : I) : (pair G (a i) (b i)).bare.Valid ∅ := by
    apply SearchTree.bare_valid
    exact compile_valid G _ _
  exact OrderedQuery.overlap_four_entropy hp (fun i => (pair G (a i) (b i)).bare)
    ht P hP hm (fun ω hω e => pair_overlap_four G a b ω (hc ω hω) e)

omit [Fintype I] in

theorem pair_transcript_left_cluster (G : BondGraph V E) (a b : V) (ω η : E → Bool)
    (h : (pair G a b).bare.run ω = (pair G a b).bare.run η) (v : V) :
    (G.openGraph {e | ω e = true}).Reachable a v ↔
      (G.openGraph {e | η e = true}).Reachable a v := by
  apply G.reachable_incidence_congr
  intro e he
  obtain ⟨x,hx,hr⟩ := he
  have hb := pair_transcript_incidence G a b ω η h e ⟨x,hx,Or.inl hr⟩
  exact congrArg (· = true) hb |>.to_iff

omit [Fintype I] in
lemma pair_transcript_right_cluster (G : BondGraph V E) (a b : V) (ω η : E → Bool)
    (h : (pair G a b).bare.run ω = (pair G a b).bare.run η) (v : V) :
    (G.openGraph {e | ω e = true}).Reachable b v ↔
      (G.openGraph {e | η e = true}).Reachable b v := by
  apply G.reachable_incidence_congr
  intro e he
  obtain ⟨x,hx,hr⟩ := he
  have hb := pair_transcript_incidence G a b ω η h e ⟨x,hx,Or.inr hr⟩
  exact congrArg (· = true) hb |>.to_iff

end CriticalPercolation.ExactExposure

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree LazyDFS

variable {V E : Type*}

def configuration (ω : E → Bool) : Set E := {e | ω e = true}

def Admissible (G : BondGraph V E) (B : Set V) (a b : V) (ω : E → Bool) (f : E) : Prop :=
  (¬∃ t ∈ B, (G.openGraph (configuration ω)).Reachable a t) ∧
    ∃ u v, G.ends f = s(u,v) ∧ (G.openGraph (configuration ω)).Reachable a u ∧
      (G.openGraph (configuration ω)).Reachable b v

lemma admissible_closed (G : BondGraph V E) (B : Set V) (a b : V) (hb : b ∈ B)
    (ω : E → Bool) (f : E) (h : Admissible G B a b ω f) : ¬configuration ω f := by
  obtain ⟨hn,u,v,hf,hu,hv⟩ := h
  intro hopen
  exact hn ⟨b,hb,hu.trans ((LazyDFS.prop_openEdge_reachable G _ hopen hf).trans hv.symm)⟩

variable [Fintype E]

lemma admissible_congr (G : BondGraph V E) (B : Set V) (a b : V) (ω η : E → Bool)
    (h : (pair G a b).bare.run ω = (pair G a b).bare.run η) (f : E) :
    Admissible G B a b ω f ↔ Admissible G B a b η f := by
  unfold Admissible
  have hl := pair_transcript_left_cluster G a b ω η h
  have hr := pair_transcript_right_cluster G a b ω η h
  simp only [configuration] at *
  simp only [hl,hr]

variable [Fintype V]

theorem pair_contact_prices (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (ω η : E → Bool)
    (h : (pair G a b).bare.run ω = (pair G a b).bare.run η) (f : E)
    (ha : Admissible G B a b ω f) (p : ℝ) (w : E → Prop → ℝ) :
    let F := fun σ : Set E => ∃ t ∈ B, (G.openGraph σ).Reachable a t
    let T := LazyDFS.search G order a B
    T.queryDelta F w (configuration ω) f = T.queryDelta F w (configuration η) f ∧
      T.prefixScore p F w (Function.update (configuration ω) f True) f =
        T.prefixScore p F w (Function.update (configuration η) f True) f := by
  obtain ⟨hn,u,v,hf,hu,hv⟩ := ha
  have hc : ¬configuration ω f := admissible_closed G B a b hb ω f ⟨hn,u,v,hf,hu,hv⟩
  have hv' : (G.openGraph (configuration η)).Reachable b v :=
    (pair_transcript_right_cluster G a b ω η h v).mp hv
  have hi : ∀ g, (∃ r ∈ G.ends g, (G.openGraph (configuration ω)).Reachable a r) →
      (configuration ω g ↔ configuration η g) := by
    rintro g ⟨r,hr,har⟩
    have hh := pair_transcript_incidence G a b ω η h g ⟨r,hr,Or.inl har⟩
    exact congrArg (· = true) hh |>.to_iff
  have hprices := LazyDFS.search_contact_reconstruction G order (configuration ω)
    (configuration η) B a u v f hf hc hn hu ⟨b,hb,hv.symm⟩ ⟨b,hb,hv'.symm⟩ hi p w 0
  dsimp only at hprices ⊢
  rw [queryDelta_update,queryDelta_update] at hprices
  exact ⟨hprices.1,hprices.2.1⟩

noncomputable def markWeight (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Bool) (f : E) : ℝ :=
  if Admissible G B a b ω f then
    p * (LazyDFS.search G order a B).queryDelta
      (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w (configuration ω) f
  else 0

noncomputable def markCost (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Bool) (f : E) : ℝ :=
  if Admissible G B a b ω f then
    (LazyDFS.search G order a B).prefixScore p
      (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w
      (Function.update (configuration ω) f True) f
  else 0

lemma pair_mark_congr (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (p : ℝ) (w : E → Prop → ℝ)
    (ω η : E → Bool) (h : (pair G a b).bare.run ω = (pair G a b).bare.run η) (f : E) :
    markWeight G order B a b p w ω f = markWeight G order B a b p w η f ∧
      markCost G order B a b p w ω f = markCost G order B a b p w η f := by
  have ha := admissible_congr G B a b ω η h f
  by_cases hf : Admissible G B a b ω f
  · have hh := pair_contact_prices G order B a b hb ω η h f hf p w
    simp only [markWeight,markCost,ite_eq_left hf,ite_eq_left (ha.mp hf)]
    exact ⟨congrArg (p * ·) hh.1,hh.2⟩
  · simp only [markWeight,markCost,ite_eq_right hf,ite_eq_right (mt ha.mpr hf),and_self]

end CriticalPercolation.ExactExposure

end
end

end OAI

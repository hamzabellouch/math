import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.CompileStop
import OAI.Probability.CriticalPercolation.GraphGeometry.MapVertices

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree BondGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

noncomputable def targetSearch (G : BondGraph V E) (B : Set V)
    (order : List (Dart (Option V) E)) (a : V) : SearchTree E (State (Option V) E) :=
  search (G.wireTargets B) order (collapseTarget B a) {none}

theorem targetSearch_moments (G : BondGraph V E) (B : Set V)
    (order : List (Dart (Option V) E)) (ho : Exhaustive (G.wireTargets B) order)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
    expect w ((targetSearch G B order a).score p F w) ≤ 1 ∧
      expect w (fun ω => ((targetSearch G B order a).score p F w ω)^2) ≤ 3 := by
  have hh := search_pivotal_moments (G.wireTargets B) order ho (collapseTarget B a) none hp w h0 h1
  have hF : (G.wireTargets B).connects (collapseTarget B a) none =
      (fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b) := by
    funext ω
    exact propext (G.wireTargets_connection B ω a)
  rw [hF] at hh
  exact hh

def GoodDarts (G : BondGraph V E) (ds : List (Dart V E)) : Prop :=
  ∀ d ∈ ds, G.ends d.2.1 = s(d.1,d.2.2)

noncomputable def mapDart (B : Set V) (d : Dart V E) : Dart (Option V) E :=
  (collapseTarget B d.1,d.2.1,collapseTarget B d.2.2)
noncomputable def mapState (B : Set V) (st : State V E) : State (Option V) E :=
  ⟨st.reached.image (collapseTarget B),st.read⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma target_hit_map (B : Set V) (st : State V E) :
    (∃ v ∈ (mapState B st).reached, v ∈ ({none} : Set (Option V))) ↔
      ∃ v ∈ st.reached, v ∈ B := by
  constructor
  · rintro ⟨v,hv,hvt⟩
    have hvn : v = none := Set.mem_singleton_iff.mp hvt
    obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp hv
    exact ⟨u,hu,(collapseTarget_eq_none B u).mp (heq.trans hvn)⟩
  · rintro ⟨v,hv,hvB⟩
    refine ⟨none,Finset.mem_image.mpr ⟨v,hv,?_⟩,Set.mem_singleton none⟩
    exact (collapseTarget_eq_none B v).mpr hvB

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma mapState_mem (B : Set V) (st : State V E)
    (hh : ¬∃ v ∈ st.reached, v ∈ B) (v : V) :
    collapseTarget B v ∈ (mapState B st).reached ↔ v ∈ st.reached := by
  constructor
  · intro hv
    obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp hv
    have huB : u ∉ B := fun hb => hh ⟨u,hu,hb⟩
    have huv := collapseTarget_injective_off B huB heq.symm
    exact huv ▸ hu
  · intro hv
    exact Finset.mem_image.mpr ⟨v,hv,rfl⟩

omit [Fintype V] [Fintype E] in
lemma mapState_closed (B : Set V) (st : State V E) (e : E) :
    mapState B (st.closed e) = (mapState B st).closed e := rfl

omit [Fintype V] [Fintype E] in
lemma mapState_opened (B : Set V) (st : State V E) (e : E) (v : V) :
    mapState B (st.opened e v) = (mapState B st).opened e (collapseTarget B v) := by
  simp [mapState,State.opened]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma mapDart_ends (G : BondGraph V E) (B : Set V) (d : Dart V E)
    (hd : G.ends d.2.1 = s(d.1,d.2.2)) :
    (G.wireTargets B).ends (mapDart B d).2.1 = s((mapDart B d).1,(mapDart B d).2.2) := by
  change Sym2.map (collapseTarget B) (G.ends d.2.1) = _
  rw [hd]; rfl

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma push_mapTarget (G : BondGraph V E) (B : Set V) (order : List (Dart V E))
    (hg : GoodDarts G order) (v : V) (hv : v ∉ B) :
    (push G order v).map (mapDart B) =
      push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B v) := by
  induction order with
  | nil => rfl
  | cons d rest ih =>
    have hd := hg d (List.mem_cons_self ..)
    have hd' := mapDart_ends G B d hd
    have hrest : GoodDarts G rest := fun d h => hg d (List.mem_cons_of_mem _ h)
    have heq : collapseTarget B d.1 = collapseTarget B v ↔ d.1 = v :=
      ⟨collapseTarget_injective_off B hv,fun h => congrArg (collapseTarget B) h⟩
    simp only [push,List.filter_cons,List.map_cons] at ih ⊢
    change (List.map (mapDart B) (if decide (d.1 = v ∧ G.ends d.2.1 = s(d.1,d.2.2)) then
      d :: rest.filter _ else rest.filter _)) = _
    simp only [hd,hd',and_true]
    change List.map (mapDart B) (if decide (d.1 = v) then d :: rest.filter _ else rest.filter _) =
      (if decide (collapseTarget B d.1 = collapseTarget B v) then
        mapDart B d :: (rest.map (mapDart B)).filter _ else (rest.map (mapDart B)).filter _)
    simp only [heq]
    split_ifs <;> simp only [List.map_cons,ih hrest]

end CriticalPercolation.LazyDFS

end
end

end OAI

import OAI.Probability.GammaPassage.GridIndependence
import OAI.Probability.GammaPassage.OriginEscape

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

abbrev PathIn := IntervalTravelBridge.PathIn
abbrev DependsOnEdges := Grid.DependsOnEdges

@[simp] theorem pathIn_iff_interval (p : Vertex) (ds : List Step) (S : Set Vertex) :
    PathIn p ds S ↔ IntervalTravelBridge.PathIn p ds S := Iff.rfl
@[simp] theorem depends_iff_grid (A : Set (Edge → ℝ)) (S : Finset Edge) :
    DependsOnEdges A S ↔ Grid.DependsOnEdges A S := Iff.rfl

def edgeEnd (e : Edge) : Vertex := e.1 + if e.2 then (0,1) else (1,0)

def internalEdges (V : Finset Vertex) : Finset Edge :=
  (V ×ˢ Finset.univ).filter (fun e => edgeEnd e ∈ V)

theorem mem_internalEdges (e : Edge) (V : Finset Vertex) :
    e ∈ internalEdges V ↔ e.1 ∈ V ∧ edgeEnd e ∈ V := by
  simp [internalEdges]

theorem internalEdges_card_le (V : Finset Vertex) : (internalEdges V).card ≤ 2*V.card := by
  have h := Finset.card_filter_le (s := V ×ˢ (Finset.univ : Finset Bool)) (fun e => edgeEnd e ∈ V)
  simpa [internalEdges,Nat.mul_comm] using h

theorem step_mem_internalEdges (V : Finset Vertex) (p : Vertex) (d : Step)
    (hp : p ∈ V) (hq : p+d.delta ∈ V) : d.edge p ∈ internalEdges V := by
  rw [mem_internalEdges]
  cases d <;> simp_all [Step.edge,Step.delta,edgeEnd,add_assoc]
  all_goals change p+0 ∈ V; simpa using hp

theorem internalEdges_disjoint {V W : Finset Vertex} (h : Disjoint V W) :
    Disjoint (internalEdges V) (internalEdges W) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact Finset.disjoint_left.mp h (mem_internalEdges e V |>.mp he).1
    (mem_internalEdges e W |>.mp hf).1

def pathEdges (p : Vertex) : List Step → Finset Edge
  | [] => ∅
  | d::ds => insert (d.edge p) (pathEdges (p+d.delta) ds)

theorem pathIn_cons_iff (p : Vertex) (d : Step) (ds : List Step) (S : Set Vertex) :
    PathIn p (d::ds) S ↔ p ∈ S ∧ PathIn (p+d.delta) ds S := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp),?_⟩
    intro i hi
    have hh := h (i+1) (by simpa using hi)
    simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh
  · rintro ⟨hp,ht⟩ i hi
    cases i with
    | zero => simpa using hp
    | succ i =>
      have hh := ht i (by simpa using hi)
      simpa only [List.take_succ_cons,displacement_cons,add_assoc] using hh

theorem pathIn_endpoint (p : Vertex) (ds : List Step) (S : Set Vertex)
    (h : PathIn p ds S) : p+displacement ds ∈ S := by
  simpa using h ds.length le_rfl

theorem pathEdges_subset_internalEdges (V : Finset Vertex) (p : Vertex) (ds : List Step)
    (h : PathIn p ds (V : Set Vertex)) : pathEdges p ds ⊆ internalEdges V := by
  induction ds generalizing p with
  | nil => simp [pathEdges]
  | cons d ds ih =>
    obtain ⟨hp,ht⟩ := (pathIn_cons_iff p d ds _).mp h
    have hq : p+d.delta ∈ V := by simpa using ht 0 (by omega)
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · rw [he]
      exact step_mem_internalEdges V p d hp hq
    · exact ih (p+d.delta) ht he

theorem pathCost_eq_of_agree (w w' : Edge → ℝ) (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ pathEdges p ds, w e=w' e) : pathCost w p ds=pathCost w' p ds := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simp only [pathCost]
    rw [h (d.edge p) (by simp [pathEdges])]
    rw [ih (p+d.delta) (fun e he => h e (by simp [pathEdges,he]))]

def strictLocalizedEvent (V : Finset Vertex) (family : Vertex → List Step → Prop)
    (bound : Vertex → List Step → ℝ) : Set (Edge → ℝ) :=
  {w | ∃ p ds, family p ds ∧ PathIn p ds (V : Set Vertex) ∧ pathCost w p ds < bound p ds}

def boundedLocalizedEvent (V : Finset Vertex) (family : Vertex → List Step → Prop)
    (bound : Vertex → List Step → ℝ) : Set (Edge → ℝ) :=
  {w | ∃ p ds, family p ds ∧ PathIn p ds (V : Set Vertex) ∧ pathCost w p ds ≤ bound p ds}

theorem measurableSet_strictLocalizedEvent (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet (strictLocalizedEvent V family bound) := by
  simpa only [strictLocalizedEvent,and_assoc] using
    measurableSet_strict_path_event (τ := fun e (w : Edge → ℝ) => w e) measurable_pi_apply
      (fun p ds => family p ds ∧ PathIn p ds (V : Set Vertex)) bound

theorem measurableSet_boundedLocalizedEvent (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    MeasurableSet (boundedLocalizedEvent V family bound) := by
  simpa only [boundedLocalizedEvent,and_assoc] using
    measurableSet_bounded_path_event (τ := fun e (w : Edge → ℝ) => w e) measurable_pi_apply
      (fun p ds => family p ds ∧ PathIn p ds (V : Set Vertex)) bound

theorem strictLocalizedEvent_depends (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    DependsOnEdges (strictLocalizedEvent V family bound) (internalEdges V) := by
  intro w w' hh
  have hc (p ds) (hin : PathIn p ds (V : Set Vertex)) : pathCost w p ds=pathCost w' p ds :=
    pathCost_eq_of_agree w w' p ds (fun e he => hh e (pathEdges_subset_internalEdges V p ds hin he))
  constructor
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [← hc p ds hin]⟩
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [hc p ds hin]⟩

theorem boundedLocalizedEvent_depends (V : Finset Vertex)
    (family : Vertex → List Step → Prop) (bound : Vertex → List Step → ℝ) :
    DependsOnEdges (boundedLocalizedEvent V family bound) (internalEdges V) := by
  intro w w' hh
  have hc (p ds) (hin : PathIn p ds (V : Set Vertex)) : pathCost w p ds=pathCost w' p ds :=
    pathCost_eq_of_agree w w' p ds (fun e he => hh e (pathEdges_subset_internalEdges V p ds hin he))
  constructor
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [← hc p ds hin]⟩
  · rintro ⟨p,ds,hf,hin,hcost⟩
    exact ⟨p,ds,hf,hin,by rwa [hc p ds hin]⟩

theorem strip_vertices_disjoint (V W : Finset Vertex) (b y z R : ℝ)
    (hV : ∀ v ∈ V, |transverse b v-y| ≤ R)
    (hW : ∀ v ∈ W, |transverse b v-z| ≤ R)
    (hsep : 2*R < |y-z|) : Disjoint V W := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have ht := abs_add_le (y-transverse b v) (transverse b v-z)
  rw [sub_add_sub_cancel,abs_sub_comm y (transverse b v)] at ht
  have h1 := hV v hv
  have h2 := hW v hw
  linarith

end GammaFPP.CrossingBridge

end OAI

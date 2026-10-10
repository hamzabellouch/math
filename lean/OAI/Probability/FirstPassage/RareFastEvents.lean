import OAI.Probability.FirstPassage.CrossingTrialGeometry
import OAI.Probability.FirstPassage.TiltedRegions

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

noncomputable def rareFastRegion (b A R s : ℝ) (n : ℤ) (t : Vertex) : Set Vertex :=
  {p | -A*(n : ℝ) ≤ ((p-t).1 : ℝ) ∧ ((p-t).1 : ℝ) ≤ (1+A)*n ∧
    |transverse b (p-t)| ≤ R*s}

theorem rareFastRegion_finite (b A R s : ℝ) (n : ℤ) (t : Vertex) :
    (rareFastRegion b A R s n t).Finite := by
  apply (finite_tilted_rectangle b t.1 (transverse b t)
    (|A*(n : ℝ)|+|(1+A)*(n : ℝ)|) (R*s)).subset
  intro p hp
  have htrans : transverse b (p-t)=transverse b p-transverse b t := by
    simp [transverse]; ring
  have hx : ((p-t).1 : ℝ)=(p.1 : ℝ)-t.1 := by simp
  refine ⟨abs_le.mpr ⟨?_,?_⟩,?_⟩
  · have := hp.1; rw [hx] at this
    linarith [le_abs_self (A*(n : ℝ)),abs_nonneg ((1+A)*(n : ℝ))]
  · have := hp.2.1; rw [hx] at this
    linarith [le_abs_self ((1+A)*(n : ℝ)),abs_nonneg (A*(n : ℝ))]
  · rw [← htrans]; exact hp.2.2

noncomputable def rareFastVertices (b A R s : ℝ) (n : ℤ) (t : Vertex) : Finset Vertex :=
  (rareFastRegion_finite b A R s n t).toFinset

@[simp] theorem mem_rareFastVertices (b A R s : ℝ) (n : ℤ) (t p : Vertex) :
    p ∈ rareFastVertices b A R s n t ↔ p ∈ rareFastRegion b A R s n t :=
  (rareFastRegion_finite b A R s n t).mem_toFinset

noncomputable def rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) : Set (Edge → ℝ) :=
  strictLocalizedEvent (rareFastVertices b A R s n t)
    (fun p ds => p.1=t.1 ∧ (p+displacement ds).1=t.1+n)
    (fun _ ds => support b m a (displacement ds)-ε*s)

theorem mem_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ rareFastEvent b m a A R ε s n t ↔
      ∃ p ds, p.1=t.1 ∧ (p+displacement ds).1=t.1+n ∧
        PathIn p ds (rareFastRegion b A R s n t) ∧ defect w b m a p ds < -ε*s := by
  simp only [rareFastEvent,strictLocalizedEvent,mem_ofPred_eq,defect]
  have hV : (rareFastVertices b A R s n t : Set Vertex)=rareFastRegion b A R s n t := by
    ext p; simp
  rw [hV]
  constructor
  · rintro ⟨p,ds,⟨hp,hq⟩,hin,hc⟩
    exact ⟨p,ds,hp,hq,hin,by linarith⟩
  · rintro ⟨p,ds,hp,hq,hin,hc⟩
    exact ⟨p,ds,⟨hp,hq⟩,hin,by linarith⟩

theorem measurableSet_rareFastEvent (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    MeasurableSet (rareFastEvent b m a A R ε s n t) :=
  measurableSet_strictLocalizedEvent _ _ _

theorem rareFastEvent_depends (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    DependsOnEdges (rareFastEvent b m a A R ε s n t)
      (internalEdges (rareFastVertices b A R s n t)) :=
  strictLocalizedEvent_depends _ _ _

theorem rareFastEvent_translate (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) (w : Edge → ℝ) :
    (fun e => w (shiftEdge t e)) ∈ rareFastEvent b m a A R ε s n 0 ↔
      w ∈ rareFastEvent b m a A R ε s n t := by
  rw [mem_rareFastEvent,mem_rareFastEvent]
  have hc (p ds) : defect (fun e => w (shiftEdge t e)) b m a p ds =
      defect w b m a (t+p) ds := by simp only [defect,pathCost_translate]
  constructor
  · rintro ⟨p,ds,hp,hq,hin,hcost⟩
    refine ⟨t+p,ds,by simpa using hp,by simpa [add_assoc] using hq,?_,?_⟩
    · intro i hi
      have he : t+p+displacement (ds.take i)-t=p+displacement (ds.take i) := by abel
      change _ ∈ rareFastRegion b A R s n t
      simpa only [rareFastRegion,mem_ofPred_eq,he,sub_zero] using hin i hi
    · rwa [← hc]
  · rintro ⟨p,ds,hp,hq,hin,hcost⟩
    refine ⟨p-t,ds,by simpa using sub_eq_zero.mpr hp,?_,?_,?_⟩
    · simp only [Prod.fst_add,Prod.fst_sub,Prod.fst_zero] at *
      omega
    · intro i hi
      have he : p-t+displacement (ds.take i)=(p+displacement (ds.take i))-t := by abel
      rw [he]
      simpa [rareFastRegion] using hin i hi
    · rw [hc,add_sub_cancel]
      exact hcost

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem rareFastEvent_probability_translate (h : ExponentialEnvironment P τ)
    (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} =
      P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n 0} := by
  have he : {ω | (fun e => τ (shiftEdge t e) ω) ∈ rareFastEvent b m a A R ε s n 0} =
      {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} := by
    ext ω
    exact rareFastEvent_translate b m a A R ε s n t (fun e => τ e ω)
  rw [← he]
  exact translated_event_probability h t _ (measurableSet_rareFastEvent ..)

theorem rareFastTrials_disjoint (b A R s : ℝ) (n X : ℤ) (Y : ℝ) (M : ℕ)
    (hR : 0 ≤ R) (hs : 1 ≤ s) :
    Pairwise (fun j l : Fin M => Disjoint
      (rareFastVertices b A R s n (trialTranslate b X Y M R s j))
      (rareFastVertices b A R s n (trialTranslate b X Y M R s l))) := by
  intro j l hjl
  apply strip_vertices_disjoint _ _ b
    (transverse b (trialTranslate b X Y M R s j))
    (transverse b (trialTranslate b X Y M R s l)) (R*s)
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · intro p hp
    have hh := ((mem_rareFastVertices ..).mp hp).2.2
    convert hh using 1
    simp [transverse]
    congr 1
    ring
  · simpa only [mul_assoc] using trial_centers_separated b X Y M R s j l hjl hR hs

theorem rareFastTrials_failure_bound (h : ExponentialEnvironment P τ)
    (b m a A R ε s p0 : ℝ) (n X : ℤ) (Y : ℝ) (M : ℕ)
    (hR : 0 ≤ R) (hs : 1 ≤ s)
    (hp0 : p0 ≤ P.real {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n 0}) :
    P.real {ω | ∀ j : Fin M, (fun e => τ e ω) ∉ rareFastEvent b m a A R ε s n
      (trialTranslate b X Y M R s j)} ≤ (1-p0)^M := by
  have hh := disjoint_trials_failure_bound h (Finset.univ : Finset (Fin M))
    (fun j => rareFastEvent b m a A R ε s n (trialTranslate b X Y M R s j))
    (fun j => internalEdges (rareFastVertices b A R s n (trialTranslate b X Y M R s j)))
    (fun _ _ => measurableSet_rareFastEvent ..) (fun j _ => rareFastEvent_depends b m a A R ε s n (trialTranslate b X Y M R s j))
    (fun _ _ _ _ hij => internalEdges_disjoint (rareFastTrials_disjoint b A R s n X Y M hR hs hij))
    p0 (fun j _ => ?_)
  · simpa using hh
  · unfold Measure.real
    rw [rareFastEvent_probability_translate h]
    exact hp0

end PlanarFPP

end OAI

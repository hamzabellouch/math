import OAI.Probability.GammaPassage.CrossingLocalized
import OAI.Probability.GammaPassage.Stationarity

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory
theorem finite_tilted_rectangle (b X Y L H : ℝ) :
    {p : Vertex | |(p.1 : ℝ)-X| ≤ L ∧ |transverse b p-Y| ≤ H}.Finite := by
  let B := |X|+|L|+|Y|+|H|+|b| *(|X|+|L|)
  obtain ⟨N,hN⟩ := exists_nat_gt B
  apply (Finset.finite_toSet (latticeBox N)).subset
  intro p hp
  obtain ⟨hpL,hpH⟩ := hp
  have hx : |(p.1 : ℝ)| ≤ |X|+|L| := by
    have hh := abs_add_le ((p.1 : ℝ)-X) X
    rw [sub_add_cancel] at hh
    linarith [le_abs_self L]
  have hy : |(p.2 : ℝ)| ≤ |Y|+|H|+|b| *(|X|+|L|) := by
    have hh := abs_add_le (transverse b p-Y) (Y+b*(p.1 : ℝ))
    have heq : transverse b p-Y+(Y+b*(p.1 : ℝ))=(p.2 : ℝ) := by unfold transverse; ring
    rw [heq] at hh
    have hh' := abs_add_le Y (b*(p.1 : ℝ))
    rw [abs_mul] at hh'
    have ht := mul_le_mul_of_nonneg_left hx (abs_nonneg b)
    linarith [le_abs_self H]
  have hxB : |(p.1 : ℝ)| < N := by
    dsimp [B] at hN
    nlinarith [abs_nonneg Y,abs_nonneg H,mul_nonneg (abs_nonneg b) (add_nonneg (abs_nonneg X) (abs_nonneg L))]
  have hyB : |(p.2 : ℝ)| < N := by
    dsimp [B] at hN
    linarith [abs_nonneg X,abs_nonneg L]
  have hx' : -(N : ℤ) ≤ p.1 ∧ p.1 ≤ N := by
    constructor
    · exact_mod_cast (abs_le.mp hxB.le).1
    · exact_mod_cast (abs_le.mp hxB.le).2
  have hy' : -(N : ℤ) ≤ p.2 ∧ p.2 ≤ N := by
    constructor
    · exact_mod_cast (abs_le.mp hyB.le).1
    · exact_mod_cast (abs_le.mp hyB.le).2
  change p ∈ latticeBox N
  simpa only [latticeBox,Finset.mem_product,Finset.mem_Icc] using And.intro hx' hy'

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

/-- Translating weights is exactly equivalent to translating all path vertices;
the supporting functional is evaluated on the unchanged displacement. -/
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
    · have he : t + (p-t) = p := by abel
      rw [hc,he]
      exact hcost

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
variable {shape rate : ℝ}

theorem rareFastEvent_probability_translate (h : GammaEnvironment shape rate P τ)
    (b m a A R ε s : ℝ) (n : ℤ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} =
      P {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n 0} := by
  have he : {ω | (fun e => τ (shiftEdge t e) ω) ∈ rareFastEvent b m a A R ε s n 0} =
      {ω | (fun e => τ e ω) ∈ rareFastEvent b m a A R ε s n t} := by
    ext ω
    exact rareFastEvent_translate b m a A R ε s n t (fun e => τ e ω)
  rw [← he]
  exact h.translated_event_probability t _ (measurableSet_rareFastEvent ..)

end GammaFPP.CrossingBridge

end OAI

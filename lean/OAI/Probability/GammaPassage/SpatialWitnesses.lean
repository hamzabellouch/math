import OAI.Probability.GammaPassage.EndpointEvents
import OAI.Probability.GammaPassage.CrossingEvents
import OAI.Probability.GammaPassage.BKPrimitives
import OAI.Probability.FirstPassage.Translation

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP Set Finset MeasureTheory ProbabilityTheory

noncomputable def translatedArbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ)
    (t : Vertex) : Set (Edge → ℝ) :=
  {w | (fun e => w (shiftEdge t e)) ∈ arbitraryEndpointEvent b m₀ a A R ε k m}

/-- Exact source event in a translated box, with unrestricted endpoints. -/
lemma mem_translatedArbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ translatedArbitraryEndpointEvent b m₀ a A R ε k m t ↔
      ∃ p ds, PathIn p ds {z | z-t ∈ endpointBox b A R k m} ∧ defect w b m₀ a p ds < -ε*(2 : ℝ)^k := by
  change (fun e => w (shiftEdge t e)) ∈ arbitraryEndpointEvent b m₀ a A R ε k m ↔ _
  rw [mem_arbitraryEndpointEvent]
  have hc (p ds) : defect (fun e => w (shiftEdge t e)) b m₀ a p ds=defect w b m₀ a (t+p) ds := by
    simp only [defect,pathCost_translate]
  constructor
  · rintro ⟨p,ds,hin,hcost⟩
    refine ⟨t+p,ds,?_,by rwa [← hc]⟩
    intro i hi
    have he : t+p+displacement (ds.take i)-t=p+displacement (ds.take i) := by abel
    simpa only [mem_ofPred_eq,he] using hin i hi
  · rintro ⟨p,ds,hin,hcost⟩
    refine ⟨p-t,ds,?_,?_⟩
    · intro i hi
      have he : p-t+displacement (ds.take i)=p+displacement (ds.take i)-t := by abel
      simpa only [mem_ofPred_eq,he] using hin i hi
    · rw [hc,add_sub_cancel]
      exact hcost

noncomputable def eitherEndpointEvent (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) : Set (Edge → ℝ) :=
  translatedArbitraryEndpointEvent b m₀ am A R ε k m t ∪
    translatedArbitraryEndpointEvent b m₀ ap A R ε k m t

lemma mem_eitherEndpointEvent (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ eitherEndpointEvent b m₀ am ap A R ε k m t ↔
      ∃ p ds, PathIn p ds {z | z-t ∈ endpointBox b A R k m} ∧
        (defect w b m₀ am p ds < -ε*(2 : ℝ)^k ∨ defect w b m₀ ap p ds < -ε*(2 : ℝ)^k) := by
  simp only [eitherEndpointEvent,mem_union,mem_translatedArbitraryEndpointEvent]
  constructor
  · rintro (⟨p,ds,hin,hc⟩ | ⟨p,ds,hin,hc⟩)
    · exact ⟨p,ds,hin,Or.inl hc⟩
    · exact ⟨p,ds,hin,Or.inr hc⟩
  · rintro ⟨p,ds,hin,hc | hc⟩
    · exact Or.inl ⟨p,ds,hin,hc⟩
    · exact Or.inr ⟨p,ds,hin,hc⟩

noncomputable def spatialTranslate (b : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Vertex :=
  (ih.1*(2 : ℤ)^m,⌊b*(ih.1*(2 : ℤ)^m)⌋+ih.2*(2 : ℤ)^k)

noncomputable def spatialRareEvent (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Set (Edge → ℝ) :=
  eitherEndpointEvent b m₀ am ap 4 4 η k m (spatialTranslate b k m ih) ∪
    crossingEvent b m₀ K ((2 : ℝ)^k) ((2 : ℤ)^m) (spatialTranslate b k m (ih+(1,0)))

/-- Exact labelled path witnesses for the two defining spatial rare events.
A support-defect witness retains which strict bound it satisfies. -/
noncomputable def spatialWitnessFamily (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Set GammaFPP.BK.StrictPathWitness :=
  {p | (PathIn p.start p.steps {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m} ∧
      (p.bound=support b m₀ am (displacement p.steps)-η*(2 : ℝ)^k ∨
       p.bound=support b m₀ ap (displacement p.steps)-η*(2 : ℝ)^k)) ∨
    (p.start.1=(spatialTranslate b k m (ih+(1,0))).1 ∧
      (p.start+displacement p.steps).1=(spatialTranslate b k m (ih+(1,0))).1+(2 : ℤ)^m ∧
      PathIn p.start p.steps (rareFastRegion b 1 8 ((2 : ℝ)^k) ((2 : ℤ)^m) (spatialTranslate b k m (ih+(1,0)))) ∧
      p.bound=m₀*(2 : ℤ)^m+K*(2 : ℝ)^k)}

lemma spatialWitness_good_event (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ)
    (p : GammaFPP.BK.StrictPathWitness) (hp : p ∈ spatialWitnessFamily b m₀ am ap K η k m ih)
    (w : Edge → ℝ) (hw : p.Good w) : w ∈ spatialRareEvent b m₀ am ap K η k m ih := by
  rcases hp with ⟨hin,hbound | hbound⟩ | ⟨hstart,hend,hin,hbound⟩
  · apply Or.inl
    apply (mem_eitherEndpointEvent ..).mpr
    refine ⟨p.start,p.steps,hin,Or.inl ?_⟩
    change pathCost w p.start p.steps < p.bound at hw
    unfold defect
    rw [hbound] at hw
    linarith
  · apply Or.inl
    apply (mem_eitherEndpointEvent ..).mpr
    refine ⟨p.start,p.steps,hin,Or.inr ?_⟩
    change pathCost w p.start p.steps < p.bound at hw
    unfold defect
    rw [hbound] at hw
    linarith
  · apply Or.inr
    refine ⟨p.start,p.steps,⟨hstart,hend⟩,?_,?_⟩
    · intro i hi
      exact (mem_rareFastVertices ..).mpr (hin i hi)
    · simpa only [GammaFPP.BK.StrictPathWitness.Good,Int.cast_pow,Int.cast_ofNat,hbound] using hw

lemma spatialRareEvent_has_witness (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ)
    (w : Edge → ℝ) (hw : w ∈ spatialRareEvent b m₀ am ap K η k m ih) :
    ∃ p ∈ spatialWitnessFamily b m₀ am ap K η k m ih, p.Good w := by
  rcases hw with hw | hw
  · obtain ⟨p,ds,hin,hc | hc⟩ := (mem_eitherEndpointEvent ..).mp hw
    · refine ⟨⟨p,ds,support b m₀ am (displacement ds)-η*(2 : ℝ)^k⟩,
        Or.inl ⟨hin,Or.inl rfl⟩,?_⟩
      change pathCost w p ds < _
      unfold defect at hc
      linarith
    · refine ⟨⟨p,ds,support b m₀ ap (displacement ds)-η*(2 : ℝ)^k⟩,
        Or.inl ⟨hin,Or.inr rfl⟩,?_⟩
      change pathCost w p ds < _
      unfold defect at hc
      linarith
  · obtain ⟨p,ds,hcols,hin,hc⟩ := hw
    refine ⟨⟨p,ds,m₀*(2 : ℤ)^m+K*(2 : ℝ)^k⟩,Or.inr ⟨hcols.1,hcols.2,?_,rfl⟩,?_⟩
    · intro i hi
      exact (mem_rareFastVertices ..).mp (hin i hi)
    · simpa only [GammaFPP.BK.StrictPathWitness.Good,Int.cast_pow,Int.cast_ofNat] using hc

lemma translatedEndpointBox_finite (b A R : ℝ) (k m : ℕ) (t : Vertex) :
    {z | z-t ∈ endpointBox b A R k m}.Finite := by
  apply ((endpointBox_finite b A R k m).image (fun p => t+p)).subset
  intro z hz
  exact ⟨z-t,hz,by abel_nf⟩

noncomputable def spatialWitnessVertices (b : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Finset Vertex :=
  (translatedEndpointBox_finite b 4 4 k m (spatialTranslate b k m ih)).toFinset ∪
    rareFastVertices b 1 8 ((2 : ℝ)^k) ((2 : ℤ)^m) (spatialTranslate b k m (ih+(1,0)))

noncomputable def spatialWitnessSupport (b : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Finset Edge :=
  internalEdges (spatialWitnessVertices b k m ih)

lemma spatialWitness_edges (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ)
    (p : GammaFPP.BK.StrictPathWitness) (hp : p ∈ spatialWitnessFamily b m₀ am ap K η k m ih) :
    p.edges ⊆ spatialWitnessSupport b k m ih := by
  apply pathEdges_subset_internalEdges
  rcases hp with ⟨hin,_⟩ | ⟨_,_,hin,_⟩
  · intro i hi
    apply Finset.mem_union.mpr
    exact Or.inl ((translatedEndpointBox_finite ..).mem_toFinset.mpr (hin i hi))
  · intro i hi
    exact Finset.mem_union.mpr (Or.inr ((mem_rareFastVertices ..).mpr (hin i hi)))

lemma spatialWitness_event_iff (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ) (w : Edge → ℝ) :
    GammaFPP.BK.StrictPathEvent (spatialWitnessSupport b k m ih) (spatialWitnessFamily b m₀ am ap K η k m ih) w ↔
      w ∈ spatialRareEvent b m₀ am ap K η k m ih := by
  constructor
  · rintro ⟨p,hp,_he,hg⟩
    exact spatialWitness_good_event b m₀ am ap K η k m ih p hp w hg
  · intro hw
    obtain ⟨p,hp,hg⟩ := spatialRareEvent_has_witness b m₀ am ap K η k m ih w hw
    exact ⟨p,hp,spatialWitness_edges b m₀ am ap K η k m ih p hp,hg⟩

noncomputable def spatialListSupport (b : ℝ) (k m : ℕ) (is : List (ℤ×ℤ)) : Finset Edge :=
  is.toFinset.biUnion (spatialWitnessSupport b k m)

end GammaFPP.CrossingBridge

end OAI

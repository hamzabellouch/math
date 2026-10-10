import OAI.Probability.FirstPassage.SpatialRareEvents
import OAI.Probability.FirstPassage.BKContinuous

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

noncomputable def spatialWitnessFamily (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Set StrictPathWitness :=
  {p | (PathIn p.start p.steps {z | z-spatialTranslate b k m ih ∈ endpointBox b 4 4 k m} ∧
      (p.bound=support b m₀ am (displacement p.steps)-η*(2 : ℝ)^k ∨
       p.bound=support b m₀ ap (displacement p.steps)-η*(2 : ℝ)^k)) ∨
    (p.start.1=(spatialTranslate b k m (ih+(1,0))).1 ∧
      (p.start+displacement p.steps).1=(spatialTranslate b k m (ih+(1,0))).1+(2 : ℤ)^m ∧
      PathIn p.start p.steps (rareFastRegion b 1 8 ((2 : ℝ)^k) ((2 : ℤ)^m) (spatialTranslate b k m (ih+(1,0)))) ∧
      p.bound=m₀*(2 : ℤ)^m+K*(2 : ℝ)^k)}

lemma spatialWitness_good_event (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ)
    (p : StrictPathWitness) (hp : p ∈ spatialWitnessFamily b m₀ am ap K η k m ih)
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
    · simpa only [StrictPathWitness.Good,Int.cast_pow,Int.cast_ofNat,hbound] using hw

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
    · simpa only [StrictPathWitness.Good,Int.cast_pow,Int.cast_ofNat] using hc

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
    (p : StrictPathWitness) (hp : p ∈ spatialWitnessFamily b m₀ am ap K η k m ih) :
    p.edges ⊆ spatialWitnessSupport b k m ih := by
  apply pathEdges_subset_internalEdges
  rcases hp with ⟨hin,_⟩ | ⟨_,_,hin,_⟩
  · intro i hi
    apply Finset.mem_union.mpr
    exact Or.inl ((translatedEndpointBox_finite ..).mem_toFinset.mpr (hin i hi))
  · intro i hi
    exact Finset.mem_union.mpr (Or.inr ((mem_rareFastVertices ..).mpr (hin i hi)))

lemma spatialWitness_event_iff (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ) (w : Edge → ℝ) :
    StrictPathEvent (spatialWitnessSupport b k m ih) (spatialWitnessFamily b m₀ am ap K η k m ih) w ↔
      w ∈ spatialRareEvent b m₀ am ap K η k m ih := by
  constructor
  · rintro ⟨p,hp,_he,hg⟩
    exact spatialWitness_good_event b m₀ am ap K η k m ih p hp w hg
  · intro hw
    obtain ⟨p,hp,hg⟩ := spatialRareEvent_has_witness b m₀ am ap K η k m ih w hw
    exact ⟨p,hp,spatialWitness_edges b m₀ am ap K η k m ih p hp,hg⟩

noncomputable def spatialListSupport (b : ℝ) (k m : ℕ) (is : List (ℤ×ℤ)) : Finset Edge :=
  is.toFinset.biUnion (spatialWitnessSupport b k m)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_spatial_witness_BK (henv : ExponentialEnvironment P τ)
    (b m₀ am ap K η p₀ : ℝ) (hp₀ : 0 ≤ p₀) (k m : ℕ)
    (hrare : ∀ ih : ℤ×ℤ, P.real {ω | (fun e => τ e ω) ∈ spatialRareEvent b m₀ am ap K η k m ih} ≤ p₀)
    (is : List (ℤ×ℤ)) :
    P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
      (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ p₀^is.length := by
  let _ := henv.probability
  let S := spatialListSupport b k m is
  have hsingle (ih : ℤ×ℤ) : P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
      (fun e => τ e ω)} ≤ p₀ := by
    apply (measureReal_mono ?_).trans (hrare ih)
    rintro ω ⟨p,hp,_he,hg⟩
    exact spatialWitness_good_event b m₀ am ap K η k m ih p hp _ hg
  apply (exponential_strict_path_BK henv S (is.map (spatialWitnessFamily b m₀ am ap K η k m))).trans
  simp only [List.map_map]
  have hprod (js : List (ℤ×ℤ)) :
      (js.map (fun ih => P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
        (fun e => τ e ω)})).prod ≤ p₀^js.length := by
    induction js with
    | nil => simp
    | cons i js ih =>
      simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ]
      calc
        _ ≤ p₀*(js.map (fun ih => P.real {ω | StrictPathEvent S (spatialWitnessFamily b m₀ am ap K η k m ih)
          (fun e => τ e ω)})).prod := mul_le_mul_of_nonneg_right (hsingle i) (List.prod_nonneg (by intro a ha; obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha; exact measureReal_nonneg))
        _ ≤ p₀*p₀^js.length := mul_le_mul_of_nonneg_left ih hp₀
        _ = _ := by ring
  exact hprod is

theorem actual_spatial_witness_BK_scales (henv : ExponentialEnvironment P τ)
    (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
    (N : ℕ) (S D : ℝ) :
    ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
      D*(2 : ℝ)^k ≤ (characteristicLength P τ actualSourceTimeConstant b q₀ k : ℝ) ∧
      ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths
        (spatialListSupport b k (characteristicExponent P τ actualSourceTimeConstant b q₀ k) is)
        (is.map (spatialWitnessFamily b (actualSourceTimeConstant (direction b))
          (extremeSlope actualSourceTimeConstant b false) (extremeSlope actualSourceTimeConstant b true)
          (sourceCrossingK actualSourceTimeConstant b) η k
          (characteristicExponent P τ actualSourceTimeConstant b q₀ k))) (fun e => τ e ω)} ≤
        (2*q₀)^is.length := by
  obtain ⟨k,hk,hs,hd,hrare⟩ := actual_spatial_rare_scales henv b q₀ η hb hq hq1 hη N S D
  refine ⟨k,hk,hs,hd,?_⟩
  intro is
  exact exponential_spatial_witness_BK henv b _ _ _ _ η (2*q₀) (by positivity) k
    (characteristicExponent P τ actualSourceTimeConstant b q₀ k) hrare is

end PlanarFPP

end OAI

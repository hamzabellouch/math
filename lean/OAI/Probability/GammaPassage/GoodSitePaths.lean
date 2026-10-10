import OAI.Probability.GammaPassage.GoodSiteEvents
import OAI.Probability.GammaPassage.CrossingEndpointBounds

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory
open scoped Topology

theorem goodSite_trial_witness (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) (w : Edge → ℝ) (hR : 0 ≤ R) (hs : 1 ≤ s)
    (hg : w ∈ goodSiteEvent μ b A R ε s plus n d M v) :
    ∃ p ds,
      p ∈ connectorWindow b (blockX n d v) (blockY (contactSign plus) (trialWindow M R s) v)
        (trialWindow M R s) ∧
      p+displacement ds ∈ connectorWindow b (blockX n d v+n)
        (blockY (contactSign plus) (trialWindow M R s) v) (trialWindow M R s) ∧
      defect w b (μ (direction b)) (extremeSlope μ b plus) p ds < -ε*s := by
  obtain ⟨j,hj⟩ := hg.1
  obtain ⟨p,ds,hp,hq,hin,hcost⟩ := (mem_rareFastEvent ..).mp hj
  have hw (q : Vertex) (hq : q ∈ rareFastRegion b A R s n
      (trialTranslate b (blockX n d v) (blockY (contactSign plus) (trialWindow M R s) v) M R s j)) :
      |transverse b q-blockY (contactSign plus) (trialWindow M R s) v| ≤ trialWindow M R s/4 := by
    apply trial_strip_in_window b (blockX n d v)
      (blockY (contactSign plus) (trialWindow M R s) v) M R s j hR hs q
    convert hq.2.2 using 1
    simp [transverse]
    congr 1
    ring
  refine ⟨p,ds,⟨hp,hw p ?_⟩,⟨hq,hw _ (pathIn_endpoint _ _ _ hin)⟩,hcost⟩
  simpa using hin 0 (by omega)

theorem sourceSupportCost_of_endpoint (μ : Plane → ℝ) (b ε s : ℝ) (plus : Bool)
    (p q : Vertex) (ds : List Step) (hd : p+displacement ds=q) :
    sourceSupportCost μ b plus ε s p q =
      support b (μ (direction b)) (extremeSlope μ b plus) (displacement ds)+ε*s/2 := by
  have he : q-p=displacement ds := by rw [← hd]; abel
  simp [sourceSupportCost,he,support,transverse,latticeEmbed]

/-- Both forward neighbors are exactly the two tested endpoint windows. -/
theorem goodSite_connector_witness (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v v' : Vertex) (w : Edge → ℝ)
    (hg : w ∈ goodSiteEvent μ b A R ε s plus n d M v)
    (hstep : v'=v+(1,0) ∨ v'=v+(0,1))
    (p q : Vertex)
    (hp : p ∈ connectorWindow b (blockX n d v+n)
      (blockY (contactSign plus) (trialWindow M R s) v) (trialWindow M R s))
    (hq : q ∈ connectorWindow b (blockX n d v')
      (blockY (contactSign plus) (trialWindow M R s) v') (trialWindow M R s)) :
    ∃ ds, p+displacement ds=q ∧
      defect w b (μ (direction b)) (extremeSlope μ b plus) p ds ≤ ε*s/2 := by
  have htest (a : ℝ) (hc : w ∈ siteConnector μ b R ε s plus n d M v a)
      (hX : blockX n d v'=blockX n d v+n+d)
      (hY : blockY (contactSign plus) (trialWindow M R s) v'=
        blockY (contactSign plus) (trialWindow M R s) v+contactSign plus*a*trialWindow M R s) :
      ∃ ds, p+displacement ds=q ∧
        defect w b (μ (direction b)) (extremeSlope μ b plus) p ds ≤ ε*s/2 := by
    have hq' := hq
    rw [hX,hY] at hq'
    obtain ⟨ds,hd,_,hcost⟩ := (mem_allPairsRegionEvent _ _ _ _ w).mp hc p hp q hq'
    refine ⟨ds,hd,?_⟩
    rw [sourceSupportCost_of_endpoint μ b ε s plus p q ds hd] at hcost
    unfold defect
    linarith
  rcases hstep with rfl | rfl
  · apply htest 1 hg.2.1
    · simp [blockX,blockLayer]; ring
    · simp [blockY,blockLevel]; ring
  · apply htest 2 hg.2.2
    · simp [blockX,blockLayer]; ring
    · simp [blockY,blockLevel]; ring

/-- At every fixed admissible scale, an infinite path of actual good sites is
incompatible with the origin shape law. Adaptive endpoint choices are allowed. -/
theorem UniformShape.no_goodSite_path (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (b A R ε s : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ)
    (hb : |b| ≤ 1) (hR : 0 ≤ R) (hε : 0 < ε) (hs : 1 ≤ s)
    (hn : 0 < n) (hd : 0 ≤ d) (hM : 0 < M)
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (hu : UniformShape w μ) :
    ¬infiniteOrientedPath (fun v => w ∈ goodSiteEvent μ b A R ε s plus n d M v) 0 := by
  rintro ⟨v,hv0,hstep,hgood⟩
  choose p trial hp hz ht using (fun t =>
    goodSite_trial_witness μ b A R ε s plus n d M (v t) w hR hs (hgood t))
  let z := fun t => p t+displacement (trial t)
  choose connector hc hcost using (fun t =>
    goodSite_connector_witness μ b A R ε s plus n d M (v t) (v (t+1)) w
      (hgood t) (hstep t) (z t) (p (t+1)) (hz t) (hp (t+1)))
  obtain ⟨initialPath,hinit⟩ := exists_path 0 (p 0)
  have hS : 0 < trialWindow M R s := by
    have := (trialWindow_scale_bounds M hM R s hR hs).1
    linarith
  obtain ⟨hescape,hbound⟩ := crossing_endpoints_escape_linear b (contactSign plus)
    (trialWindow M R s) n d hb (abs_contactSign plus) hS hn hd v z hv0 hstep
    (fun t => (hz t).1) (fun t => (hz t).2)
  have hf : ∀ u : Plane, μ (direction b)*u 0+extremeSlope μ b plus*(u 1-b*u 0) ≤ μ u := by
    have hh := planar_extreme_supports μ hμ b
    cases plus
    · exact hh.1
    · exact hh.2.1
  apply hu.no_crossing_chain w hw μ b (μ (direction b)) (extremeSlope μ b plus) (ε*s)
    (2*((n : ℝ)+d)+3*trialWindow M R s) (by positivity) (by
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
      positivity) hf initialPath trial connector p z (by simpa using hinit)
    (fun _ => rfl) hc (fun t => by have := (ht t).le; linarith) hcost hescape hbound

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- The almost-sure uniform Gamma shape theorem gives probability zero for
an infinite good-site path. -/
theorem gamma_goodSite_path_probability_zero (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε s : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ)
    (hb : |b| ≤ 1) (hR : 0 ≤ R) (hε : 0 < ε) (hs : 1 ≤ s)
    (hn : 0 < n) (hd : 0 ≤ d) (hM : 0 < M) :
    P {ω | infiniteOrientedPath (fun v => (fun e => τ e ω) ∈
      goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n d M v) 0}=0 := by
  have hh : ∀ᵐ ω ∂P, ¬infiniteOrientedPath (fun v => (fun e => τ e ω) ∈
      goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n d M v) 0 := by
    filter_upwards [h.ae_positive,h.uniform_shape hshape hrate] with ω hw hu
    exact UniformShape.no_goodSite_path (gammaMeanNorm h hshape hrate) (gammaMeanNorm_laws h hshape hrate) b A R ε s plus n d M hb hR hε hs hn hd hM
      (fun e => τ e ω) (fun e => (hw e).le) hu
  simpa only [ae_iff,not_not] using hh

end GammaFPP.CrossingBridge

end OAI

import OAI.Probability.GammaPassage.GoodSiteTrials

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem internalEdges_mono {V W : Finset Vertex} (h : V ⊆ W) :
    internalEdges V ⊆ internalEdges W := by
  intro e he
  obtain ⟨hp,hq⟩ := (mem_internalEdges e V).mp he
  exact (mem_internalEdges e W).mpr ⟨h hp,h hq⟩

theorem DependsOnEdges.mono {E : Set (Edge → ℝ)} {S T : Finset Edge}
    (h : DependsOnEdges E S) (hst : S ⊆ T) : DependsOnEdges E T := by
  intro w w' hh
  exact h w w' (fun e he => hh e (hst he))

theorem rareFastVertices_subset_block (b A R s σ : ℝ) (n d : ℤ) (v : Vertex)
    (M : ℕ) (j : Fin M) (_hA : 0 ≤ A) (hn : 0 ≤ n) (hR : 0 ≤ R) (hs : 1 ≤ s) :
    rareFastVertices b A R s n
      (trialTranslate b (blockX n d v) (blockY σ (trialWindow M R s) v) M R s j) ⊆
      blockVertices b A n d σ (trialWindow M R s) v := by
  intro p hp
  have hh := (mem_rareFastVertices ..).mp hp
  have htrans : transverse b (p-trialTranslate b (blockX n d v)
      (blockY σ (trialWindow M R s) v) M R s j)=transverse b p-
      transverse b (trialTranslate b (blockX n d v) (blockY σ (trialWindow M R s) v) M R s j) := by
    simp [transverse]; ring
  have hw := trial_strip_in_window b (blockX n d v) (blockY σ (trialWindow M R s) v)
    M R s j hR hs p (by rw [← htrans]; exact hh.2.2)
  have hS : 0 ≤ trialWindow M R s := by
    have := (trialWindow_scale_bounds M j.pos R s hR hs).1
    linarith
  rw [mem_blockVertices]
  refine ⟨abs_le.mpr ⟨?_,?_⟩,by linarith⟩
  · have hl := hh.1
    simp only [Prod.fst_sub,trialTranslate,Int.cast_sub] at hl
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  · have hu := hh.2.1
    simp only [Prod.fst_sub,trialTranslate,Int.cast_sub] at hu
    have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith

theorem connectorVertices_subset_block (b A s σ S : ℝ) (n d : ℤ) (v : Vertex)
    (hA : 0 ≤ A) (hd : 0 ≤ d) (_hs : 0 ≤ s) (hn : (d : ℝ)+s ≤ n) :
    connectorVertices b (blockX n d v+n) d (blockY σ S v) S s ⊆
      blockVertices b A n d σ S v := by
  intro p hp
  have hh := (mem_connectorVertices ..).mp hp
  rw [mem_blockVertices]
  refine ⟨abs_le.mpr ⟨?_,?_⟩,hh.2.2⟩
  all_goals
    have hl := hh.1
    have hu := hh.2.1
    simp only [Int.cast_add] at hl hu
    have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
    have hn' : (0 : ℝ) ≤ n := by linarith
    nlinarith

noncomputable def siteTrial (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) (j : Fin M) : Set (Edge → ℝ) :=
  rareFastEvent b (μ (direction b)) (extremeSlope μ b plus) A R ε s n
    (trialTranslate b (blockX n d v) (blockY (contactSign plus) (trialWindow M R s) v) M R s j)

noncomputable def siteConnector (μ : Plane → ℝ) (b R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) (a : ℝ) : Set (Edge → ℝ) :=
  allPairsRegionEvent
    (connectorVertices b (blockX n d v+n) d
      (blockY (contactSign plus) (trialWindow M R s) v) (trialWindow M R s) s)
    (connectorWindow b (blockX n d v+n)
      (blockY (contactSign plus) (trialWindow M R s) v) (trialWindow M R s))
    (connectorWindow b (blockX n d v+n+d)
      (blockY (contactSign plus) (trialWindow M R s) v+contactSign plus*a*trialWindow M R s)
      (trialWindow M R s))
    (sourceSupportCost μ b plus ε s)

noncomputable def goodSiteEvent (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) : Set (Edge → ℝ) :=
  {w | (∃ j : Fin M, w ∈ siteTrial μ b A R ε s plus n d M v j) ∧
    w ∈ siteConnector μ b R ε s plus n d M v 1 ∧
    w ∈ siteConnector μ b R ε s plus n d M v 2}

theorem measurableSet_goodSiteEvent (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) :
    MeasurableSet (goodSiteEvent μ b A R ε s plus n d M v) := by
  change MeasurableSet ({w | ∃ j : Fin M, w ∈ siteTrial μ b A R ε s plus n d M v j} ∩
    (siteConnector μ b R ε s plus n d M v 1 ∩ siteConnector μ b R ε s plus n d M v 2))
  apply MeasurableSet.inter
  · simp only [ofPred_exists]
    exact MeasurableSet.iUnion (fun j => measurableSet_rareFastEvent ..)
  · exact (measurableSet_allPairsRegionEvent ..).inter (measurableSet_allPairsRegionEvent ..)

theorem goodSiteEvent_depends (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool)
    (n d : ℤ) (M : ℕ) (v : Vertex) (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hR : 0 ≤ R) (hs : 1 ≤ s) (hn : (d : ℝ)+s ≤ n) :
    DependsOnEdges (goodSiteEvent μ b A R ε s plus n d M v)
      (internalEdges (blockVertices b A n d (contactSign plus) (trialWindow M R s) v)) := by
  have hn0 : 0 ≤ n := by
    have : (0 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have ht (j : Fin M) : DependsOnEdges (siteTrial μ b A R ε s plus n d M v j)
      (internalEdges (blockVertices b A n d (contactSign plus) (trialWindow M R s) v)) :=
    (rareFastEvent_depends b (μ (direction b)) (extremeSlope μ b plus) A R ε s n _).mono
      (internalEdges_mono (rareFastVertices_subset_block b A R s (contactSign plus) n d v M j hA hn0 hR hs))
  have hc (a : ℝ) : DependsOnEdges (siteConnector μ b R ε s plus n d M v a)
      (internalEdges (blockVertices b A n d (contactSign plus) (trialWindow M R s) v)) :=
    (allPairsRegionEvent_depends _ _ _ _).mono
      (internalEdges_mono (connectorVertices_subset_block b A s (contactSign plus)
        (trialWindow M R s) n d v hA hd (by linarith) hn))
  intro w w' hh
  change ((∃ j, w ∈ siteTrial μ b A R ε s plus n d M v j) ∧ _ ∧ _) ↔ _
  exact and_congr (exists_congr (fun j => ht j w w' hh))
    (and_congr (hc 1 w w' hh) (hc 2 w w' hh))

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem goodSiteEvent_independent (h : GammaEnvironment shape rate P τ)
    (μ : Plane → ℝ) (b A R ε s : ℝ) (plus : Bool) (n d : ℤ) (M : ℕ)
    (hM : 0 < M) (hA : 0 < A) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hs : 1 ≤ s) (hn : (d : ℝ)+s ≤ n) :
    SeparatedGoodIndependent P
      (fun v => {ω | (fun e => τ e ω) ∈ goodSiteEvent μ b A R ε s plus n d M v})
      (⌈4*(A+3)+8⌉₊+1) := by
  have hn0 : 0 < n := by
    have : (0 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  have hS : 0 < trialWindow M R s := by
    have := (trialWindow_scale_bounds M hM R s hR hs).1
    linarith
  exact block_supported_tests_independent h b A n d (contactSign plus) (trialWindow M R s)
    hn0 hd (abs_contactSign plus) hS hA _ (fun v => measurableSet_goodSiteEvent ..)
    (fun v => goodSiteEvent_depends μ b A R ε s plus n d M v hA.le hd hR hs hn)

end GammaFPP.CrossingBridge

end OAI

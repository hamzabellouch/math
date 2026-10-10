import OAI.Probability.FirstPassage.EndpointCoarseGeometry

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory ProbabilityTheory

lemma endpointBox_finite (b A R : ℝ) (k m : ℕ) : (endpointBox b A R k m).Finite := by
  simpa [endpointBox] using finite_tilted_rectangle b 0 0 (A*(2 : ℝ)^m) (R*(2 : ℝ)^k)

noncomputable def endpointBoxVertices (b A R : ℝ) (k m : ℕ) : Finset Vertex :=
  (endpointBox_finite b A R k m).toFinset

noncomputable def arbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) : Set (Edge → ℝ) :=
  strictLocalizedEvent (endpointBoxVertices b A R k m) (fun _ _ => True)
    (fun _ ds => support b m₀ a (displacement ds)-ε*(2 : ℝ)^k)

lemma mem_arbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) (w : Edge → ℝ) :
    w ∈ arbitraryEndpointEvent b m₀ a A R ε k m ↔
      ∃ p ds, PathIn p ds (endpointBox b A R k m) ∧ defect w b m₀ a p ds < -ε*(2 : ℝ)^k := by
  have hv : (endpointBoxVertices b A R k m : Set Vertex)=endpointBox b A R k m :=
    (endpointBox_finite b A R k m).coe_toFinset
  simp only [arbitraryEndpointEvent,strictLocalizedEvent,mem_ofPred_eq,true_and,hv,defect]
  constructor <;> rintro ⟨p,ds,hin,hc⟩ <;> exact ⟨p,ds,hin,by linarith⟩

lemma measurableSet_arbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) :
    MeasurableSet (arbitraryEndpointEvent b m₀ a A R ε k m) :=
  measurableSet_strictLocalizedEvent _ _ _

lemma arbitraryEndpointEvent_depends (b m₀ a A R ε : ℝ) (k m : ℕ) :
    DependsOnEdges (arbitraryEndpointEvent b m₀ a A R ε k m)
      (internalEdges (endpointBoxVertices b A R k m)) := strictLocalizedEvent_depends _ _ _

noncomputable def coarsePairIndices (A : ℝ) (J : ℕ) : Finset (ℤ×ℤ) :=
  ((coarseColumnIndices A J) ×ˢ (coarseColumnIndices A J)).filter (fun ij => ij.1 < ij.2)

noncomputable def coarsePairEvent (b m₀ a A R ε : ℝ) (k m J : ℕ) (ij : ℤ×ℤ) : Set (Edge → ℝ) :=
  rareFastEvent b m₀ a (coarseRegionFactor A J) (R+1) (ε/2) ((2 : ℝ)^k)
    (gridMesh m J*ij.2-gridMesh m J*ij.1) (endpointVertex b 0 (gridMesh m J*ij.1))

theorem arbitraryEndpointEvent_coarse_cover (b m₀ K A R a ε : ℝ)
    (hK : 0 ≤ K) (hm : 0 < m₀) (hA : 0 ≤ A) (hR : 0 ≤ R) (hε : 0 < ε)
    (k m J : ℕ) (hJ : 1 ≤ J) (hJlast : J ≤ gridLastLevel m) (hlast : gridLastLevel m ≤ k)
    (herror : 2*endpointExtensionError K k J+2*|a| ≤ ε*(2 : ℝ)^k/2)
    (hscale : (2*R*|a| /m₀)*(2 : ℝ)^k ≤ (gridMesh m J : ℝ)) :
    arbitraryEndpointEvent b m₀ a A R ε k m ⊆
      (gridConnectionsEvent b m₀ K A R k m J)ᶜ ∪
        ⋃ ij ∈ coarsePairIndices A J,coarsePairEvent b m₀ a A (R+2*(K+200)) ε k m J ij := by
  intro w hw
  by_cases hg : w ∈ gridConnectionsEvent b m₀ K A R k m J
  · apply Or.inr
    obtain ⟨p,ds,hin,hcost⟩ := (mem_arbitraryEndpointEvent ..).mp hw
    obtain ⟨X,Y,hXd,hYd,hX,hY,hspan,q,es,hq,he,hpath,hdef⟩ :=
      gridConnections_extend_negative_path w b m₀ K A R a ε hK hm hR hε k m J hJ hJlast hlast hg
        herror hscale p ds hin hcost
    obtain ⟨i,hi,hXi⟩ := coarse_column_index A hA m J X hXd hX
    obtain ⟨j,hj,hYj⟩ := coarse_column_index A hA m J Y hYd hY
    have hij : i < j := by
      have hd := gridMesh_pos m J
      have hspan' : gridMesh m J ≤ Y-X := by exact_mod_cast hspan
      rw [hXi,hYj] at hspan'
      nlinarith
    apply mem_iUnion₂.mpr
    refine ⟨(i,j),mem_filter.mpr ⟨mem_product.mpr ⟨hi,hj⟩,hij⟩,?_⟩
    apply (mem_rareFastEvent ..).mpr
    refine ⟨q,es,?_,?_,?_,hdef⟩
    · simpa only [endpointVertex] using hq.trans hXi
    · simp only [endpointVertex]
      rw [he,hYj]
      ring
    · intro t ht
      have hz := endpointBox_into_rareFastRegion b A (R+2*(K+200)) hA k m J X Y hX hspan (hpath t ht)
      simpa only [hXi,hYj] using hz
  · exact Or.inl hg

end PlanarFPP

end OAI

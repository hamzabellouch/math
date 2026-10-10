import OAI.Probability.GammaPassage.EndpointEvents
import OAI.Probability.GammaPassage.RareFast

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- Uniform over all positive coarse spans. The rare-fast estimate is used
in its full joint form, before selecting any endpoint pair at a given scale. -/
theorem gamma_coarsePair_bound (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (hA : 0 < A) (hR : 0 ≤ R) (hε : 0 < ε)
    (plus : Bool) (J : ℕ) (κ : ℝ) (hκ : 0 < κ) :
    ∃ S D : ℝ, 1 ≤ S ∧ 0 < D ∧ ∀ k m : ℕ, S ≤ (2 : ℝ)^k →
      D*(2 : ℝ)^k ≤ (gridMesh m J : ℝ) → ∀ ij ∈ coarsePairIndices A J,
      P.real {ω | (fun e => τ e ω) ∈
        coarsePairEvent b ((gammaMeanNorm henv hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm henv hshape hrate) b plus) A R ε k m J ij} < κ := by
  obtain ⟨S,D,hS,hD,hbound⟩ := gamma_rareFast_bound henv hshape hrate b
    (coarseRegionFactor A J) (R+1) (ε/2) hb (by unfold coarseRegionFactor; positivity)
    (by linarith) (by linarith) plus κ hκ
  refine ⟨S,D,hS,hD,?_⟩
  intro k m hs hd ij hij
  have hij' := (mem_filter.mp hij).2
  have hmesh := gridMesh_pos m J
  have hn : gridMesh m J ≤ gridMesh m J*ij.2-gridMesh m J*ij.1 := by
    have hh : ij.1+1 ≤ ij.2 := by omega
    nlinarith
  have hnR : (gridMesh m J : ℝ) ≤ ((gridMesh m J*ij.2-gridMesh m J*ij.1 : ℤ) : ℝ) := by exact_mod_cast hn
  have hh := hbound ((2 : ℝ)^k) hs _ (hd.trans hnR)
  unfold coarsePairEvent Measure.real
  rw [rareFastEvent_probability_translate henv]
  exact hh

/-- Actual arbitrary-endpoint probability is bounded by grid failure plus a
fixed finite collection of jointly rare positive-span crossings. -/
theorem gamma_arbitraryEndpoint_probability_bound (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b K A R ε : ℝ) (hb : |b| ≤ 1) (hK : 100 ≤ K) (hm : 0 < (gammaMeanNorm henv hshape hrate) (direction b))
    (hA : 0 < A) (hR : 0 < R) (hε : 0 < ε) (plus : Bool)
    (J : ℕ) (hJ : 1 ≤ J) (κ : ℝ) (hκ : 0 < κ) :
    ∃ S D : ℝ, 1 ≤ S ∧ 0 < D ∧ ∀ k m : ℕ,
      J ≤ gridLastLevel m → gridLastLevel m ≤ k → S ≤ (2 : ℝ)^k →
      D*(2 : ℝ)^k ≤ (gridMesh m J : ℝ) →
      2*endpointExtensionError shape rate K k J+2*|extremeSlope (gammaMeanNorm henv hshape hrate) b plus| ≤ ε*(2 : ℝ)^k/2 →
      (2*R*|extremeSlope (gammaMeanNorm henv hshape hrate) b plus| /((gammaMeanNorm henv hshape hrate) (direction b)))*(2 : ℝ)^k ≤ (gridMesh m J : ℝ) →
      P.real {ω | (fun e => τ e ω) ∈
        arbitraryEndpointEvent b ((gammaMeanNorm henv hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm henv hshape hrate) b plus) A R ε k m} ≤
      P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b ((gammaMeanNorm henv hshape hrate) (direction b)) K A R k m J}+
        ((coarsePairIndices A J).card : ℝ)*κ := by
  let _ := henv.probability
  obtain ⟨S,D,hS,hD,hbound⟩ := gamma_coarsePair_bound henv hshape hrate b A (R+2*(Grid.attachmentAllowance shape rate K)) ε
    hb hA (by
      have ha := Grid.attachmentAllowance_ge_fifty hshape hrate hK
      linarith) hε plus J κ hκ
  refine ⟨S,D,hS,hD,?_⟩
  intro k m hJl hlast hs hd herror hscale
  let G : Set Ω := {ω | (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b ((gammaMeanNorm henv hshape hrate) (direction b)) K A R k m J}
  let E (ij : ℤ×ℤ) : Set Ω := {ω | (fun e => τ e ω) ∈
    coarsePairEvent b ((gammaMeanNorm henv hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm henv hshape hrate) b plus) A (R+2*(Grid.attachmentAllowance shape rate K)) ε k m J ij}
  have hsub : {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b ((gammaMeanNorm henv hshape hrate) (direction b))
      (extremeSlope (gammaMeanNorm henv hshape hrate) b plus) A R ε k m} ⊆ G ∪ ⋃ ij ∈ coarsePairIndices A J,E ij := by
    intro ω hω
    have hh := arbitraryEndpointEvent_coarse_cover shape rate b ((gammaMeanNorm henv hshape hrate) (direction b)) K A R (extremeSlope (gammaMeanNorm henv hshape hrate) b plus)
      ε hshape hrate hK hm hA.le hR.le hε k m J hJ hJl hlast herror hscale hω
    rcases hh with hh | hh
    · exact Or.inl hh
    · obtain ⟨ij,hij,he⟩ := mem_iUnion₂.mp hh
      exact Or.inr (mem_iUnion₂.mpr ⟨ij,hij,he⟩)
  calc
    _ ≤ P.real (G ∪ ⋃ ij ∈ coarsePairIndices A J,E ij) :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
    _ ≤ P.real G+P.real (⋃ ij ∈ coarsePairIndices A J,E ij) := measureReal_union_le _ _
    _ ≤ P.real G+∑ ij ∈ coarsePairIndices A J,P.real (E ij) :=
      add_le_add le_rfl (measureReal_biUnion_finset_le _ _)
    _ ≤ P.real G+∑ _ij ∈ coarsePairIndices A J,κ :=
      add_le_add le_rfl (sum_le_sum (fun ij hij => (hbound k m hs hd ij hij).le))
    _ = _ := by simp [G]

end GammaFPP.CrossingBridge

end OAI

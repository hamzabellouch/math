import OAI.Geometry.Immersion.ClosedSurface.AtlasMargins
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes PhaseGrid

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι]

abbrev AtlasPhaseLabel := ι × Fin (Fintype.card PhaseGrid.Label)

def atlasPhaseLabel (a : ι × (Index × Fin 3)) : Fin (Fintype.card (AtlasPhaseLabel (ι := ι))) :=
  Fintype.equivFin (AtlasPhaseLabel (ι := ι)) (a.1,phaseLabel a.2)

lemma atlas_phase_label_count : Fintype.card (AtlasPhaseLabel (ι := ι)) = Fintype.card ι * 108 := by
  simp [AtlasPhaseLabel,PhaseGrid.Label]



omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
theorem atlas_distinct_labels_on_intersection (p : ι → M) (ψ : ι → M → ℝ)
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (s : ι → Finset Index) {h : ℝ} (hh : 0 < h)
    {a b : ι × (Index × Fin 3)} (hab : a ≠ b) {q : M}
    (ha : q ∈ tsupport (refinedCutoff (p a.1) (ψ a.1) (s a.1) h a.2.1))
    (hb : q ∈ tsupport (refinedCutoff (p b.1) (ψ b.1) (s b.1) h b.2.1)) :
    atlasPhaseLabel a ≠ atlasPhaseLabel b := by
  intro he
  have hl := (Fintype.equivFin (AtlasPhaseLabel (ι := ι))).injective he
  have hi : a.1 = b.1 := congrArg (fun x : AtlasPhaseLabel (ι := ι) => x.1) hl
  rcases a with ⟨i,a⟩
  rcases b with ⟨j,b⟩
  simp only at hi
  subst j
  have hab' : a ≠ b := fun he => hab (congrArg (fun x => (i,x)) he)
  have hca := normalizedCutoff_tsupport (s i) h a.1
    (refinedCutoff_tsupport_inner (p i) (hsource i) (s i) h a.1 ha)
  have hcb := normalizedCutoff_tsupport (s i) h b.1
    (refinedCutoff_tsupport_inner (p i) (hsource i) (s i) h b.1 hb)
  exact distinct_labels_on_intersection hh hab' hca hcb (congrArg (fun x : AtlasPhaseLabel (ι := ι) => x.2) hl)

end ClosedSurfaceR4

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] {ι : Type*} [Fintype ι]



theorem finite_atlas_transition_bounds (p : ι → M) (ψ : ι → M → ℝ)
    (hsource : ∀ i, tsupport (ψ i) ⊆ (chartAt Plane (p i)).source)
    (hcompact : ∀ i, HasCompactSupport (ψ i)) :
    ∃ d L : ℝ, 0 < d ∧ 0 < L ∧ ∀ i j : ι,
      ∀ x ∈ coordinateChart (p i) '' (tsupport (ψ i) ∩ tsupport (ψ j)),
        d ≤ |coordDet (fderiv ℝ (coordinateTransition (p j) (p i)) x)| ∧
        ‖fderiv ℝ (coordinateTransition (p j) (p i)) x‖ ≤ L := by
  classical
  have hs (i : ι) : tsupport (ψ i) ⊆ (coordinateChart (p i)).source := by
    rw [coordinateChart_source]
    exact hsource i
  have hb (a : ι × ι) : ∃ d L : ℝ, 0 < d ∧ 0 < L ∧
      ∀ x ∈ coordinateChart (p a.1) '' (tsupport (ψ a.1) ∩ tsupport (ψ a.2)),
        d ≤ |coordDet (fderiv ℝ (coordinateTransition (p a.2) (p a.1)) x)| ∧
        ‖fderiv ℝ (coordinateTransition (p a.2) (p a.1)) x‖ ≤ L := by
    have hK := (hcompact a.1).inter_right (isClosed_tsupport (ψ a.2))
    exact coordinateTransition_compact_bounds (p a.2) (p a.1)
      (coordinateChart_compact_image hK (p a.1) (fun x hx => hs a.1 hx.1))
      (coordinateChart_image_overlap (p a.2) (p a.1)
        (fun x hx => hs a.1 hx.1) (fun x hx => hs a.2 hx.2))
  choose d L hd hL hbound using hb
  obtain ⟨d₀,hd₀,_,hle⟩ := finite_positive_threshold d hd
  refine ⟨d₀,1+∑ a, L a,hd₀,?_,?_⟩
  · have hn : 0 ≤ ∑ a, L a := Finset.sum_nonneg (fun a _ => le_of_lt (hL a))
    linarith
  · intro i j x hx
    refine ⟨(hle (i,j)).trans ((hbound (i,j) x hx).1),?_⟩
    have hsL : L (i,j) ≤ ∑ a, L a :=
      Finset.single_le_sum (fun a _ => le_of_lt (hL a)) (Finset.mem_univ (i,j))
    exact ((hbound (i,j) x hx).2).trans (by linarith)

end ClosedSurfaceR4

end

end OAI

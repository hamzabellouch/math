import OAI.Probability.SLE.Geometry.CompactConnectedNeighborhoods
import Mathlib.Topology.Connected.LocallyPathConnected

namespace OAI

/-! Compact trace sets admit small paths, including after adjoining a
compact interval of the real boundary. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology NNReal

namespace SLEExactGauge

lemma finiteTrace_locallyPathConnected {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (T : ℝ≥0) :
    LocallyPathConnectedSpace (γ '' Icc 0 T) := by
  have : LocallyPathConnectedSpace (Icc (0:ℝ) (T:ℝ)) :=
    (isQuotientMap_projIcc (a := (0:ℝ)) (b := (T:ℝ)) (h := T.coe_nonneg)).locallyPathConnectedSpace
  let p : Icc (0:ℝ) (T:ℝ) → γ '' Icc 0 T := fun t =>
    ⟨γ t.1.toNNReal,⟨t.1.toNNReal,⟨by simp,(Real.toNNReal_le_iff_le_coe).mpr t.2.2⟩,rfl⟩⟩
  have hp : Continuous p := (hγ.comp (continuous_real_toNNReal.comp continuous_subtype_val)).subtype_mk _
  have hs : Surjective p := by
    rintro ⟨z,t,ht,rfl⟩
    refine ⟨⟨t,⟨t.coe_nonneg,by exact_mod_cast ht.2⟩⟩,?_⟩
    apply Subtype.ext
    simp [p]
  exact (hp.isClosedMap.isQuotientMap hp hs).locallyPathConnectedSpace

lemma compact_union_locallyPathConnected {X : Type*} [TopologicalSpace X] [T2Space X]
    {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    [LocallyPathConnectedSpace A] [LocallyPathConnectedSpace B] :
    LocallyPathConnectedSpace ↥(A∪B) := by
  have : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let p : A⊕B → ↥(A∪B) := Sum.elim
    (fun a => ⟨a.1,Or.inl a.2⟩) (fun b => ⟨b.1,Or.inr b.2⟩)
  have hp : Continuous p := continuous_sum_dom.mpr
    ⟨continuous_subtype_val.subtype_mk _,continuous_subtype_val.subtype_mk _⟩
  have hs : Surjective p := by
    rintro ⟨x,hx⟩
    rcases hx with hx | hx
    · exact ⟨Sum.inl ⟨x,hx⟩,rfl⟩
    · exact ⟨Sum.inr ⟨x,hx⟩,rfl⟩
  exact (hp.isClosedMap.isQuotientMap hp hs).locallyPathConnectedSpace

lemma compact_locallyPathConnected_uniform_path {A : Type*} [MetricSpace A]
    [CompactSpace A] [LocallyPathConnectedSpace A] (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ ∀ x y : A, dist x y<δ →
      ∃ p : Path x y, ∀ t, dist (p t) x<ε := by
  classical
  have hlocal (a : A) : ∃ V : Set A, V∈𝓝 a ∧ IsPathConnected V ∧ V⊆ball a (ε/2) := by
    obtain ⟨V,⟨hV,hpc⟩,hsub⟩ := (path_connected_basis a).mem_iff.mp
      (ball_mem_nhds a (half_pos hε))
    exact ⟨V,hV,hpc,hsub⟩
  choose V hV hc hs using hlocal
  obtain ⟨δ,hδ,hcover⟩ := Metric.uniformity_basis_dist.lebesgue_number_lemma_nhds
    (K := (univ : Set A)) isCompact_univ (fun a _ => hV a)
  refine ⟨δ,hδ,fun x y hxy => ?_⟩
  obtain ⟨a,ha⟩ := hcover x (mem_univ x)
  have hsub : ball x δ⊆V a := by
    intro z hz
    apply ha
    change dist x z<δ
    simpa only [mem_ball,dist_comm] using hz
  have hx := hsub (mem_ball_self hδ)
  have hy := hsub (by simpa only [mem_ball,dist_comm] using hxy)
  obtain ⟨p,hp⟩ := hc a |>.joinedIn x hx y hy
  refine ⟨p,fun t => ?_⟩
  have ht := mem_ball.mp (hs a (hp t))
  have hx' := mem_ball.mp (hs a hx)
  have htri := dist_triangle (p t) a x
  rw [dist_comm a x] at htri
  linarith

end SLEExactGauge

end

end OAI

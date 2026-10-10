import OAI.Geometry.SurfaceImmersion.Whitney.CornerBridgeEmbedding
import OAI.Geometry.SurfaceImmersion.Geometry.FinitePointNeighborhoods

namespace OAI

/-! Simultaneous separated smooth bridges at finitely many path corners,
with attachment points inside prescribed parameter windows. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [Finite ι]
variable {p q : M} {γ : Path p q}

theorem finite_corner_bridges (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) (T : ι → ℝ) (hT : Function.Injective T)
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (haT : ∀ i, a i < T i)
    (hTb : ∀ i, T i < b i) (hb : ∀ i, b i ≤ 1)
    {O : Set M} (hO : IsOpen O) (hTO : ∀ i, γ.extend (T i) ∈ O) :
    ∃ B : ∀ i, LocalCornerBridge γ (T i) O,
      (∀ i, a i < (B i).left ∧ (B i).right < b i) ∧
      (∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
        ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
          (B i).arc.curve s ≠ γ.extend u) ∧
      Pairwise (fun i j => Disjoint
        ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
        ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish)) := by
  classical
  have hTi : ∀ i, T i ∈ Ioo (0:ℝ) 1 := fun i =>
    ⟨lt_of_le_of_lt (ha i) (haT i),lt_of_lt_of_le (hTb i) (hb i)⟩
  choose U hU hTU hUO hUavoid using fun i =>
    embedded_path_corner_neighborhood γ hi (ha i) (haT i) (hTb i) (hb i) hO (hTO i)
  have hp : Function.Injective (fun i => γ.extend (T i)) := by
    intro i j hij
    exact hT (embeddedPath_extend_injOn γ hi ⟨(hTi i).1.le,(hTi i).2.le⟩
      ⟨(hTi j).1.le,(hTi j).2.le⟩ hij)
  obtain ⟨V,hV,hVdis⟩ := finite_disjoint_open_neighborhoods (fun i => γ.extend (T i)) hp U hU hTU
  choose B hBsep using fun i => separated_corner_bridge hγ hi (hTi i) (hV i).1 (hV i).2.1
  let B' : ∀ i, LocalCornerBridge γ (T i) O := fun i => (B i).mono ((hV i).2.2.trans (hUO i))
  have hbounds : ∀ i, a i < (B i).left ∧ (B i).right < b i := by
    intro i
    constructor
    · apply lt_of_not_ge
      intro hle
      apply hUavoid i (B i).left (Or.inl ⟨(B i).left_pos.le,hle⟩)
      have hm := (hV i).2.2 ((B i).image_subset
        (left_mem_Icc.mpr (B i).arc.start_lt_finish.le))
      have he := (B i).source_eq
      rw [he] at hm
      have he' : γ.extend (B i).left = γ (B i).leftPoint := Path.extend_extends' γ (B i).leftPoint
      rwa [he']
    · apply lt_of_not_ge
      intro hle
      apply hUavoid i (B i).right (Or.inr ⟨hle,(B i).right_lt_one.le⟩)
      have hm := (hV i).2.2 ((B i).image_subset
        (right_mem_Icc.mpr (B i).arc.start_lt_finish.le))
      have he := (B i).target_eq
      rw [he] at hm
      have he' : γ.extend (B i).right = γ (B i).rightPoint := Path.extend_extends' γ (B i).rightPoint
      rwa [he']
  refine ⟨B',hbounds,hBsep,?_⟩
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨s,hs,hxs⟩ ⟨u,hu,hxu⟩
  have hxVi : x ∈ V i := by
    rw [← hxs]
    exact (B i).image_subset hs
  have hxVj : x ∈ V j := by
    rw [← hxu]
    exact (B j).image_subset hu
  exact disjoint_left.mp (hVdis hij) hxVi hxVj

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

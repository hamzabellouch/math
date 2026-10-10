import OAI.Geometry.SurfaceImmersion.Whitney.FiniteCornerBridges
import OAI.Geometry.SurfaceImmersion.Whitney.FiniteCornerWindows
import Mathlib.Data.Finset.Sort

namespace OAI

/-! The actual finite nonsmooth parameter set can be rounded by an ordered
family of mutually disjoint smooth bridges. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {p q : M} {γ : Path p q}

theorem ordered_corner_bridges_interior (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) {O : Set M} (hO : IsOpen O)
    (hγO : ∀ t ∈ Ioo (0:ℝ) 1, γ.extend t ∈ O) :
    ∃ (n : ℕ) (T : Fin n → ℝ), StrictMono T ∧
      (∀ i, T i ∈ Ioo (0:ℝ) 1) ∧
      ∃ B : ∀ i, LocalCornerBridge γ (T i) O,
        (∀ i j, i < j → (B i).right < (B j).left) ∧
        (∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
          ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
            (B i).arc.curve s ≠ γ.extend u) ∧
        Pairwise (fun i j => Disjoint
          ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
          ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish)) ∧
        ∀ t ∈ Ioo (0:ℝ) 1, t ∉ range T →
          ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
          Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t) := by
  classical
  obtain ⟨S,hS,hregular⟩ := hγ.smooth_outside_finite hi
  let F : Finset ℝ := hS.toFinset.filter (fun t => t ∈ Ioo (0:ℝ) 1)
  let T : Fin F.card → ℝ := F.orderEmbOfFin rfl
  have hTm : StrictMono T := (F.orderEmbOfFin rfl).strictMono
  have hTi : ∀ i, T i ∈ Ioo (0:ℝ) 1 := by
    intro i
    exact (Finset.mem_filter.mp (F.orderEmbOfFin_mem rfl i)).2
  obtain ⟨a,b,hab,_,horder⟩ := finite_corner_windows T hTm.injective hTi
  have hTO : ∀ i, γ.extend (T i) ∈ O := fun i => hγO _ (hTi i)
  obtain ⟨B,hB,hsep,hdis⟩ := finite_corner_bridges hγ hi T hTm.injective a b
    (fun i => (hab i).1.le) (fun i => (hab i).2.1) (fun i => (hab i).2.2.1)
    (fun i => (hab i).2.2.2.le) hO hTO
  refine ⟨F.card,T,hTm,hTi,B,?_,hsep,hdis,?_⟩
  · intro i j hij
    exact (hB i).2.trans ((horder i j (hTm hij)).trans (hB j).1)
  · intro t ht hn
    apply hregular t ht
    intro hts
    have htF : t ∈ F := Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hts,ht⟩
    apply hn
    have hr : range T = (F : Set ℝ) := F.range_orderEmbOfFin rfl
    rw [hr]
    exact htF

theorem ordered_corner_bridges (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) {O : Set M} (hO : IsOpen O)
    (hγO : range γ ⊆ O) :
    ∃ (n : ℕ) (T : Fin n → ℝ), StrictMono T ∧
      (∀ i, T i ∈ Ioo (0:ℝ) 1) ∧
      ∃ B : ∀ i, LocalCornerBridge γ (T i) O,
        (∀ i j, i < j → (B i).right < (B j).left) ∧
        (∀ i, ∀ s ∈ Icc (B i).arc.start (B i).arc.finish,
          ∀ u ∈ Ico (0:ℝ) (B i).left ∪ Ioc (B i).right 1,
            (B i).arc.curve s ≠ γ.extend u) ∧
        Pairwise (fun i j => Disjoint
          ((B i).arc.curve '' Icc (B i).arc.start (B i).arc.finish)
          ((B j).arc.curve '' Icc (B j).arc.start (B j).arc.finish)) ∧
        ∀ t ∈ Ioo (0:ℝ) 1, t ∉ range T →
          ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
          Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t) := by
  apply ordered_corner_bridges_interior hγ hi hO
  intro t ht
  rw [Path.extend_apply γ ⟨ht.1.le,ht.2.le⟩]
  exact hγO (mem_range_self _)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

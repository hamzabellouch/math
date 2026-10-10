import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceArcTimeCoordinates
import Mathlib.Topology.UnitInterval

namespace OAI

/-! A finite ordered subdivision of the actual embedded arc, in charts
which all use the same global longitudinal coordinate. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

structure SurfaceTimeChart (F : M → ℝ) where
  coord : OpenPartialHomeomorph M Base
  smooth : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ coord coord.source
  inverse_smooth : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ coord.symm coord.target
  time : ∀ x ∈ coord.source, coord x 1 = F x

theorem arc_time_chart_partition (P : SmoothCompactArc planeModel M)
    {F : M → ℝ} (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    (hFP : ∀ s ∈ Icc P.start P.finish, F (P.curve s) = s) :
    ∃ (τ : ℕ → ℝ) (N : ℕ), τ 0 = P.start ∧ Monotone τ ∧
      (∀ n, τ n ∈ Icc P.start P.finish) ∧ (∀ n ≥ N, τ n = P.finish) ∧
      ∀ n, ∃ c : SurfaceTimeChart F,
        ∀ s ∈ Icc (τ n) (τ (n+1)), P.curve s ∈ c.coord.source ∧ c.coord (P.curve s) = ![0,s] := by
  classical
  choose d J hJ htJ hds hdi hdF haxis using
    fun t : Icc P.start P.finish => surface_arc_time_coordinates P hF hFP t.property
  let C : Icc P.start P.finish → Set (Icc P.start P.finish) :=
    fun t => (fun s : Icc P.start P.finish => (s:ℝ)) ⁻¹' J t
  have hC : ∀ t, IsOpen (C t) := fun t => (hJ t).preimage continuous_subtype_val
  have hcover : univ ⊆ ⋃ t, C t := by
    intro t _
    exact mem_iUnion.mpr ⟨t,htJ t⟩
  obtain ⟨τ,hzero,hmono,⟨N,hend⟩,hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc P.start_lt_finish.le hC hcover
  refine ⟨fun n => (τ n:ℝ),N,hzero,fun _ _ h => hmono h,fun n => (τ n).property,hend,?_⟩
  intro n
  obtain ⟨t,ht⟩ := hsub n
  refine ⟨⟨d t,hds t,hdi t,hdF t⟩,?_⟩
  intro s hs
  have hsP : s ∈ Icc P.start P.finish :=
    ⟨(τ n).property.1.trans hs.1,hs.2.trans (τ (n+1)).property.2⟩
  have hsJ : s ∈ J t := ht (show (⟨s,hsP⟩ : Icc P.start P.finish) ∈ Icc (τ n) (τ (n+1)) from hs)
  refine ⟨(haxis t s hsJ).1,?_⟩
  exact (haxis t s hsJ).2.trans (by rw [hFP s hsP])

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.Immersion.ClosedSurface.AtlasPhases

namespace OAI

/-! Good phase directions pass between surface coordinate charts. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry

lemma PhaseGeometry.Good.tensor_ne_zero {n : ℕ} {B : Fin 3 → RVec n} {ξ : Base}
    (h : Good B ξ) : B ≠ 0 := by
  intro hz
  apply h.2
  simp [hz,secondQuadratic]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

/-- The quantitative overlap theorem implies the qualitative phase
condition, with no externally supplied determinant or size constants. -/
theorem actual_phase_good_at {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source)
    (ξ : Base)
    (hD : NormalFrame.gramDet
      (coordDeriv dx (coordinateMap F q) (coordinateChart q a))
      (coordDeriv dy (coordinateMap F q) (coordinateChart q a)) ≠ 0)
    (hgood : Good (realSecondTensor (coordinateMap F q) (coordinateChart q a)) ξ) :
    Good (realSecondTensor (coordinateMap F p) (coordinateChart p a))
      (atlasPhaseCovector q p ξ a) := by
  let B := realSecondTensor (coordinateMap F q) (coordinateChart q a)
  let c := ‖secondQuadratic B (-ξ.2,ξ.1)‖
  let ε := c/(‖B‖+1)
  have hc : 0 < c := norm_pos_iff.mpr hgood.2
  have hd : 0 < ‖B‖+1 := by positivity
  have hε : 0 < ε := div_pos hc hd
  have hm : ε*‖B‖ ≤ c := by
    calc
      ε*‖B‖ ≤ ε*(‖B‖+1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = c := by dsimp [ε]; field_simp
  obtain ⟨η,L,_,_,ht⟩ := compact_overlap_phase_margin
    (K := ({a} : Set M)) isCompact_singleton q p
    (fun x hx => by simpa only [mem_singleton_iff.mp hx] using hap)
    (fun x hx => by simpa only [mem_singleton_iff.mp hx] using haq)
  have hx : coordinateChart p a ∈ coordinateChart p '' ({a} : Set M) :=
    ⟨a,by simp,rfl⟩
  have he := coordinateTransition_apply_chart q p hap
  have hresult := ht F hF (coordinateChart p a) hx ξ ε hε
    (by simpa only [he] using hD)
    (by simpa only [he] using hgood.tensor_ne_zero)
    (by simpa only [he] using hm)
  have hx' := coordinateTransition_mem_chart q p hap haq
  simpa only [atlasPhaseCovector,actual_phase_differential q p ξ hx'] using hresult.2.2.1

end ClosedSurfaceR4

end

end OAI

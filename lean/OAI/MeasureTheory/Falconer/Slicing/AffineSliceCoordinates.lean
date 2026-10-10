import OAI.MeasureTheory.Falconer.Slicing.SliceCoordinates
import OAI.MeasureTheory.Falconer.Measures.StartingMeasures

namespace OAI

/-! # Isometric coordinates and ball bounds on an actual charged affine plane -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

noncomputable def affineSliceMap (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p x : Space d) : Space n :=
  slicePointCoordinates V hn (x-p)

noncomputable def affineSliceModel (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p : Space d) (x : Space n) : Space d :=
  p + ((sliceCoordinates V hn).symm x : Space d)

theorem affineSliceMap_continuous (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p : Space d) : Continuous (affineSliceMap V hn p) :=
  (slicePointCoordinates_continuous V hn).comp (continuous_id.sub continuous_const)

theorem affineSliceModel_isometry (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p : Space d) : Isometry (affineSliceModel V hn p) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (p + ((sliceCoordinates V hn).symm x : Space d))
    (p + ((sliceCoordinates V hn).symm y : Space d)) = dist x y
  rw [dist_add_left]
  exact (sliceCoordinates V hn).symm.isometry.dist_eq x y

theorem affineSliceModel_mem (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p : Space d) (x : Space n) :
    affineSliceModel V hn p x-p ∈ V := by
  simpa only [affineSliceModel,add_sub_cancel_left] using ((sliceCoordinates V hn).symm x).property

theorem affineSliceMap_model (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p : Space d) (x : Space n) :
    affineSliceMap V hn p (affineSliceModel V hn p x) = x := by
  simp only [affineSliceMap,affineSliceModel,add_sub_cancel_left,slicePointCoordinates,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,LinearIsometryEquiv.apply_symm_apply]

theorem affineSliceModel_map (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p x : Space d) (hx : x-p ∈ V) :
    affineSliceModel V hn p (affineSliceMap V hn p x) = x := by
  have he : V.orthogonalProjectionOnto (x-p) = (⟨x-p,hx⟩ : V) :=
    V.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x-p,hx⟩
  simp only [affineSliceModel,affineSliceMap,slicePointCoordinates,he,
    LinearIsometryEquiv.symm_apply_apply,Subtype.coe_mk]
  abel

theorem affineSliceMap_dist (V : Submodule ℝ (Space d))
    (hn : Module.finrank ℝ V = n) (p x : Space d) (hx : x-p ∈ V) (y : Space n) :
    dist (affineSliceMap V hn p x) y = dist x (affineSliceModel V hn p y) := by
  have he := (affineSliceModel_isometry V hn p).dist_eq (affineSliceMap V hn p x) y
  rw [affineSliceModel_map V hn p x hx] at he
  exact he.symm

theorem affineSliceMap_frostman (μ : Measure (Space d))
    (V : Submodule ℝ (Space d)) (hn : Module.finrank ℝ V = n) (p : Space d)
    (hplane : μ {x | x-p ∈ V}ᶜ = 0) {s C : ℝ} (hfrost : FrostmanBallBound μ s C) :
    FrostmanBallBound (μ.map (affineSliceMap V hn p)) s C := by
  intro y r hr
  rw [Measure.map_apply (affineSliceMap_continuous V hn p).measurable Metric.isOpen_ball.measurableSet]
  apply le_trans _ (hfrost (affineSliceModel V hn p y) r hr)
  apply measure_mono_ae
  have hplane' : ∀ᵐ x ∂μ, x-p ∈ V := hplane
  filter_upwards [hplane'] with x hx
  intro hxy
  simpa only [mem_preimage,Metric.mem_ball,affineSliceMap_dist V hn p x hx y] using hxy

end Falconer

end OAI

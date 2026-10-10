import OAI.Geometry.NodalSets.Charts.LocalAdaptedFrame
import OAI.Geometry.NodalSets.Charts.MetricConnectionFamilyLemmas

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

def frameMap (e : Fin 4 → Coord) : Coord →L[ℝ] Coord :=
  ∑ i : Fin 4, (ContinuousLinearMap.proj i).smulRight (e i)

lemma frameMap_apply (e : Fin 4 → Coord) (x : Coord) : frameMap e x = ∑ i, x i • e i := by
  simp [frameMap]

lemma frameMap_axis (e : Fin 4 → Coord) (i : Fin 4) : frameMap e (Pi.single i 1) = e i := by
  simp [frameMap_apply, Pi.single_apply, ite_smul, eq_comm]

lemma frameMap_pair (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (e : Fin 4 → Coord)
    (he : ∀ i j, g (e i) (e j) = if i = j then 1 else 0) (x : Coord) (i : Fin 4) :
    g (e i) (frameMap e x) = x i := by
  simp [frameMap_apply, map_sum, he, mul_ite]

lemma frameMap_injective (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (e : Fin 4 → Coord)
    (he : ∀ i j, g (e i) (e j) = if i = j then 1 else 0) : Function.Injective (frameMap e) := by
  intro x y hxy
  ext i
  rw [← frameMap_pair g e he x i, ← frameMap_pair g e he y i, hxy]

def frameEquiv (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (e : Fin 4 → Coord)
    (he : ∀ i j, g (e i) (e j) = if i = j then 1 else 0) : Coord ≃L[ℝ] Coord :=
  ((frameMap e).toLinearMap.linearEquivOfInjective (frameMap_injective g e he) rfl).toContinuousLinearEquiv

lemma frameEquiv_coe (g : Coord →L[ℝ] Coord →L[ℝ] ℝ) (e : Fin 4 → Coord)
    (he : ∀ i j, g (e i) (e j) = if i = j then 1 else 0) :
    (frameEquiv g e he).toContinuousLinearMap = frameMap e := rfl

variable {T : Type*} [TopologicalSpace T]
lemma frameMap_continuous (e : T → Fin 4 → Coord) (he : ∀ i, Continuous (fun t ↦ e t i)) :
    Continuous (fun t ↦ frameMap (e t)) := by
  apply continuous_finsetSum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ Coord Coord (ContinuousLinearMap.proj i)).continuous.comp (he i)

theorem frameEquiv_continuous (g : T → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (e : T → Fin 4 → Coord) (he : ∀ i, Continuous (fun t ↦ e t i))
    (hortho : ∀ t i j, g t (e t i) (e t j) = if i = j then 1 else 0) :
    Continuous (fun t ↦ (frameEquiv (g t) (e t) (hortho t)).toContinuousLinearMap) :=
  frameMap_continuous e he

lemma frameConnection_continuous (B : T → Coord →L[ℝ] Coord →L[ℝ] Coord)
    (e : T → Coord ≃L[ℝ] Coord) (hB : Continuous B)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap)) :
    Continuous (fun t ↦ frameConnection (B t) (e t)) := by
  exact (((ContinuousLinearMap.compL ℝ Coord Coord Coord).flip.continuous.comp he).clm_comp hB).clm_comp he

theorem quadratic_chart_maps_joint_continuous (y : T → Coord) (hy : Continuous y)
    (B : T → Coord →L[ℝ] Coord →L[ℝ] Coord) (hB : Continuous B)
    (e : T → Coord ≃L[ℝ] Coord) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap)) :
    Continuous (fun z : T × Coord ↦ quadraticChartMap (y z.1) (e z.1)
      (frameConnection (B z.1) (e z.1)) z.2) := by
  have hC : Continuous (fun z : T × Coord ↦ frameConnection (B z.1) (e z.1)) :=
    (frameConnection_continuous B e hB he).comp continuous_fst
  exact ((hy.comp continuous_fst).add ((he.comp continuous_fst).clm_apply continuous_snd)).sub
    ((hC.clm_apply continuous_snd).clm_apply continuous_snd |>.const_smul (1/2:ℝ))

end
end Yau.Geometry

end OAI

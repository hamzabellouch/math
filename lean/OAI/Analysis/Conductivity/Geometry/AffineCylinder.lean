import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CollarLpPullback
import OAI.Analysis.Conductivity.Variational.AxialDecayL2

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

def affineEndTime (a b : ℝ) (t : ℝ) : ℝ := a*(t-b)

def affineEndCoordinates (a b : ℝ) : ℝ×UnitAddTorus (Fin 2) → ℝ×UnitAddTorus (Fin 2) :=
  Prod.map (affineEndTime a b) id

lemma measurable_affineEndTime (a b : ℝ) : Measurable (affineEndTime a b) := by
  unfold affineEndTime; fun_prop

lemma measurable_affineEndCoordinates (a b : ℝ) : Measurable (affineEndCoordinates a b) :=
  (measurable_affineEndTime a b).prodMap measurable_id

lemma affineEndTime_volume {a : ℝ} (ha : a≠0) (b : ℝ) :
    Measure.map (affineEndTime a b) volume=ENNReal.ofReal |a⁻¹| • volume := by
  have he : affineEndTime a b=(fun t => a*t) ∘ (fun t : ℝ => t+(-b)) := by
    funext t; simp [affineEndTime,sub_eq_add_neg]
  rw [he,←Measure.map_map (f:=fun t : ℝ => t+(-b)) (g:=fun t : ℝ => a*t)
    (by fun_prop) (by fun_prop),map_add_right_eq_self,Real.map_volume_mul_left ha]

lemma affineEndTime_interval_le {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) :
    Measure.map (affineEndTime a b) (volume.restrict (Ioc l r)) ≤
      ENNReal.ofReal |a⁻¹| • FiniteAxisMeasure R := by
  have hS : Ioc l r⊆(affineEndTime a b) ⁻¹' Icc 0 R := fun t ht => hT t ⟨ht.1.le,ht.2⟩
  have hle : Measure.map (affineEndTime a b) (volume.restrict (Ioc l r)) ≤
      (Measure.map (affineEndTime a b) volume).restrict (Icc 0 R) := by
    rw [Measure.restrict_map (measurable_affineEndTime a b) measurableSet_Icc]
    exact Measure.map_mono (Measure.restrict_mono hS le_rfl) (measurable_affineEndTime a b)
  have hcc : volume.restrict (Icc (0:ℝ) R)=FiniteAxisMeasure R := by
    exact Measure.restrict_congr_set (Ioc_ae_eq_Icc' (measure_singleton (0:ℝ))).symm
  rwa [affineEndTime_volume ha,Measure.restrict_smul,hcc] at hle

lemma affineEndCoordinates_interval_le {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) :
    Measure.map (affineEndCoordinates a b) (sourceCylinderMeasure l r) ≤
      ENNReal.ofReal |a⁻¹| • sourceCylinderMeasure 0 R := by
  unfold sourceCylinderMeasure
  rw [affineEndCoordinates,←Measure.map_prod_map _ _ (measurable_affineEndTime a b) measurable_id,
    Measure.map_id,←Measure.prod_smul_left]
  exact Measure.prod_mono (affineEndTime_interval_le ha hT) le_rfl

def affineEndPullback {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) :
    Lp ℂ 2 (sourceCylinderMeasure 0 R) →L[ℝ] Lp ℂ 2 (sourceCylinderMeasure l r) :=
  ((Lp.compMeasurePreservingₗᵢ ℝ (affineEndCoordinates a b)
    ⟨measurable_affineEndCoordinates a b,rfl⟩).toContinuousLinearMap).comp
      (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (affineEndCoordinates_interval_le ha hT))

lemma affineEndPullback_ae {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (f : Lp ℂ 2 (sourceCylinderMeasure 0 R)) :
    affineEndPullback ha hT f=ᵐ[sourceCylinderMeasure l r] f ∘ affineEndCoordinates a b := by
  have h0 := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (affineEndCoordinates_interval_le ha hT) f
  have h1 := Lp.coeFn_compMeasurePreserving
    (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (affineEndCoordinates_interval_le ha hT) f)
    (show MeasurePreserving (affineEndCoordinates a b) (sourceCylinderMeasure l r)
      (Measure.map (affineEndCoordinates a b) (sourceCylinderMeasure l r)) from
      ⟨measurable_affineEndCoordinates a b,rfl⟩)
  exact h1.trans ((show Measure.QuasiMeasurePreserving (affineEndCoordinates a b) (sourceCylinderMeasure l r)
    (Measure.map (affineEndCoordinates a b) (sourceCylinderMeasure l r)) from
    ⟨measurable_affineEndCoordinates a b,Measure.absolutelyContinuous_rfl⟩).ae_eq_comp h0)

lemma affineEndPullback_ae_of_ae {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (f : Lp ℂ 2 (sourceCylinderMeasure 0 R)) {g : ℝ×UnitAddTorus (Fin 2) → ℂ}
    (hg : f=ᵐ[sourceCylinderMeasure 0 R] g) :
    affineEndPullback ha hT f=ᵐ[sourceCylinderMeasure l r] g ∘ affineEndCoordinates a b := by
  apply (affineEndPullback_ae ha hT f).trans
  have hq : Measure.QuasiMeasurePreserving (affineEndCoordinates a b) (sourceCylinderMeasure l r)
      (sourceCylinderMeasure 0 R) :=
    ⟨measurable_affineEndCoordinates a b,
      Measure.absolutelyContinuous_of_le_smul (affineEndCoordinates_interval_le ha hT)⟩
  exact hq.ae_eq_comp hg

end ScalarConductivity

end

end OAI

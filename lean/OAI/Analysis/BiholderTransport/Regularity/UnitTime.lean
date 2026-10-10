import Mathlib

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
abbrev UnitTime := Icc (0:ℝ) 1
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : Fact ((0:ℝ) ≤ 1) := ⟨zero_le_one⟩

def extendUnitPath (u : C(UnitTime,E)) : C(ℝ,E) :=
  u.comp (ContinuousMap.projIccCM (a := (0:ℝ)) (b := 1))

omit [NormedSpace ℝ E] in
@[simp] lemma extendUnitPath_coe (u : C(UnitTime,E)) (t : UnitTime) :
    extendUnitPath u t = u t := by
  change u (projIcc 0 1 (by positivity) t) = u t
  rw [projIcc_of_mem _ t.property]

omit [NormedSpace ℝ E] in
@[simp] lemma extendUnitPath_add (u v : C(UnitTime,E)) :
    extendUnitPath (u+v) = extendUnitPath u + extendUnitPath v := rfl

@[simp] lemma extendUnitPath_smul (c : ℝ) (u : C(UnitTime,E)) :
    extendUnitPath (c • u) = c • extendUnitPath u := rfl

def unitPathPrimitive (u : C(UnitTime,E)) : C(UnitTime,E) :=
  ⟨fun t => ∫ s in (0:ℝ)..t.val, extendUnitPath u s,
   (intervalIntegral.continuous_primitive
      (fun a b => (extendUnitPath u).continuous.intervalIntegrable a b) 0).comp
      continuous_subtype_val⟩

lemma unitPathPrimitive_bound (u : C(UnitTime,E)) : ‖unitPathPrimitive u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
  intro t
  change ‖∫ s in (0:ℝ)..t.val, extendUnitPath u s‖ ≤ ‖u‖
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := t.val) (f := extendUnitPath u)
    (C := ‖u‖) (fun s _ => u.norm_coe_le_norm (projIcc 0 1 (by positivity) s))
  apply h.trans
  rw [sub_zero,abs_of_nonneg t.property.1]
  exact mul_le_of_le_one_right (norm_nonneg u) t.property.2

def unitPathIntegral : C(UnitTime,E) →L[ℝ] C(UnitTime,E) := by
  let L : C(UnitTime,E) →ₗ[ℝ] C(UnitTime,E) :=
    { toFun := unitPathPrimitive
      map_add' := by
        intro u v; ext t
        change (∫ s in (0:ℝ)..t.val, extendUnitPath (u+v) s) =
          (∫ s in (0:ℝ)..t.val, extendUnitPath u s) +
          (∫ s in (0:ℝ)..t.val, extendUnitPath v s)
        rw [extendUnitPath_add]
        exact intervalIntegral.integral_add
          ((extendUnitPath u).continuous.intervalIntegrable _ _)
          ((extendUnitPath v).continuous.intervalIntegrable _ _)
      map_smul' := by
        intro c u; ext t
        change (∫ s in (0:ℝ)..t.val, extendUnitPath (c • u) s) =
          c • (∫ s in (0:ℝ)..t.val, extendUnitPath u s)
        rw [extendUnitPath_smul]
        exact intervalIntegral.integral_smul c (extendUnitPath u) }
  exact L.mkContinuous 1 (by
    intro u
    change ‖unitPathPrimitive (u : C(UnitTime,E))‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using unitPathPrimitive_bound u)

@[simp] lemma unitPathIntegral_apply (u : C(UnitTime,E)) (t : UnitTime) :
    unitPathIntegral u t = ∫ s in (0:ℝ)..t.val, extendUnitPath u s := rfl

lemma hasDerivAt_unitPathPrimitive [CompleteSpace E] (u : C(UnitTime,E)) (t : ℝ) :
    HasDerivAt (fun s => ∫ r in (0:ℝ)..s, extendUnitPath u r) (extendUnitPath u t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((extendUnitPath u).continuous.intervalIntegrable 0 t)
    (extendUnitPath u).continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    (extendUnitPath u).continuous.continuousAt

end WeakMTWTransport

end

end OAI

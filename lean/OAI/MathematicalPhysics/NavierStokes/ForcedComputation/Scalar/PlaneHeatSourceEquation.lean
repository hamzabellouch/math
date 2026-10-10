import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildDerivatives
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatSourceJetDerivative
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetIntegral

namespace OAI

/-! Spatial derivatives and the time equation of the actual Gaussian source integral. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild
open ShearFlows Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

theorem heatSourcePath_directional {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (v : Plane) (q : WeaklySingular.Path (Jet (k+1)) T) :
    directionalPath k v T (heatSourcePath hT hν (k+1) q) =
      heatSourcePath hT hν k (directionalPath k v T q) := by
  apply (WeaklySingular.pathEquiv (Jet k) T).injective
  apply ContinuousMap.ext
  intro t
  change BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k v
    (heatSourcePath hT hν (k+1) q t) = _
  simp only [heatSourcePath_apply]
  exact rawKernelIntegral_directional hT hν k v q 0 t

theorem function_heatSourcePath {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (q : WeaklySingular.Path (Jet k) T) (t : Icc (0 : ℝ) T) (x : Plane) :
    BoundedSpatialJets.function Plane ℝ k (heatSourcePath hT hν k q t) x =
      ∫ s in 0..t.val, PlaneHeat.evolution ℝ
        (BoundedSpatialJets.function Plane ℝ k (WeaklySingular.extendPath (Jet k) hT q s))
        (ν*(t.val-s)) x := by
  rw [heatSourcePath_apply, BoundedSpatialJets.function_intervalIntegral]
  · apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne t.val] with s hs hst
    rw [uIoc_of_le t.property.1] at hst
    have hp : 0 < t.val-s := sub_pos.mpr (lt_of_le_of_ne hst.2 hs)
    rw [rawHeatKernel_pos hν k hp, PlaneHeat.heatOperator_apply]
    rw [PlaneHeat.evolution, ite_eq_right (not_le.mpr (mul_pos hν hp)),
      PlaneHeat.heatConvolution_eq]
    rfl
  · exact rawKernel_path_integrable hT hν k q 0 t

theorem spatialPartial_heatSourcePath {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (j : Fin 2) (q : WeaklySingular.Path (Jet (k+1)) T)
    (t : Icc (0 : ℝ) T) (x : Plane) :
    PlaneHeat.spatialPartial ℝ j
      (BoundedSpatialJets.function Plane ℝ (k+1) (heatSourcePath hT hν (k+1) q t)) x =
        BoundedSpatialJets.function Plane ℝ k
          (heatSourcePath hT hν k (directionalPath k (Pi.single j 1) T q) t) x := by
  rw [← heatSourcePath_directional hT hν k (Pi.single j 1) q]
  change _ = BoundedSpatialJets.function Plane ℝ k
    (BoundedSpatialJets.directionalDerivativeCLM Plane ℝ k (Pi.single j 1)
      (heatSourcePath hT hν (k+1) q t)) x
  exact (BoundedSpatialJets.function_directionalDerivativeCLM Plane ℝ k (Pi.single j 1) _ x).symm

theorem spatialPartial_twice_heatSourcePath {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (k : ℕ) (j : Fin 2) (q : WeaklySingular.Path (Jet (k+2)) T)
    (t : Icc (0 : ℝ) T) (x : Plane) :
    PlaneHeat.spatialPartial ℝ j (PlaneHeat.spatialPartial ℝ j
      (BoundedSpatialJets.function Plane ℝ (k+2) (heatSourcePath hT hν (k+2) q t))) x =
        BoundedSpatialJets.function Plane ℝ k
          (heatSourcePath hT hν k
            (directionalPath k (Pi.single j 1) T (directionalPath (k+1) (Pi.single j 1) T q)) t) x := by
  have he := funext (spatialPartial_heatSourcePath hT hν (k+1) j q t)
  rw [he]
  exact spatialPartial_heatSourcePath hT hν k j _ t x

/-- The bounded source is continued constantly in time outside the finite slab. -/
def sourceValue {T : ℝ} (hT : 0 ≤ T) (k : ℕ) (q : WeaklySingular.Path (Jet k) T)
    (s : ℝ) (x : Plane) : ℝ :=
  BoundedSpatialJets.function Plane ℝ k (WeaklySingular.extendPath (Jet k) hT q s) x

/-- Scalar value of the source integral, with the same constant time continuation. -/
def heatSourceValue {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν) (k : ℕ)
    (q : WeaklySingular.Path (Jet k) T) (s : ℝ) (x : Plane) : ℝ :=
  sourceValue hT k (heatSourcePath hT hν k q) s x

theorem sourceValue_directional {T : ℝ} (hT : 0 ≤ T) (k : ℕ) (j : Fin 2)
    (q : WeaklySingular.Path (Jet (k+1)) T) (s : ℝ) :
    sourceValue hT k (directionalPath k (Pi.single j 1) T q) s =
      PlaneHeat.spatialPartial ℝ j (sourceValue hT (k+1) q s) := by
  funext x
  unfold sourceValue
  rw [extendPath_directional, BoundedSpatialJets.function_directionalDerivativeCLM]
  rfl

theorem sourceValue_twice_directional {T : ℝ} (hT : 0 ≤ T) (k : ℕ) (j : Fin 2)
    (q : WeaklySingular.Path (Jet (k+2)) T) (s : ℝ) :
    sourceValue hT k
      (directionalPath k (Pi.single j 1) T (directionalPath (k+1) (Pi.single j 1) T q)) s =
        PlaneHeat.spatialPartial ℝ j (PlaneHeat.spatialPartial ℝ j (sourceValue hT (k+2) q s)) := by
  rw [sourceValue_directional, sourceValue_directional]

theorem hasDerivAt_heatSourceValue {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (q : WeaklySingular.Path (Jet 3) T)
    (hq : ∀ s, ContDiff ℝ ∞ (sourceValue hT 3 q s))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Plane) :
    HasDerivAt (fun s => heatSourceValue hT hν 3 q s x)
      (ν * ∑ j : Fin 2, PlaneHeat.spatialPartial ℝ j
        (PlaneHeat.spatialPartial ℝ j (heatSourceValue hT hν 3 q t)) x + sourceValue hT 3 q t x) t := by
  let J : C(ℝ, Jet 3) := ⟨WeaklySingular.extendPath (Jet 3) hT q,
    WeaklySingular.continuous_extendPath (Jet 3) hT q⟩
  have hd := PlaneHeat.hasDerivAt_heat_source_of_jets ℝ hν ht.1
    (sourceValue hT 3 q) hq J (fun _ _ => rfl) ‖q‖
    (WeaklySingular.norm_extendPath_le (Jet 3) hT q) x
  have he : (fun s => heatSourceValue hT hν 3 q s x) =ᶠ[𝓝 t]
      (fun s => ∫ r in 0..s, PlaneHeat.evolution ℝ (sourceValue hT 3 q r) (ν*(s-r)) x) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    unfold heatSourceValue sourceValue WeaklySingular.extendPath
    rw [projIcc_of_mem hT ⟨hs.1.le, hs.2.le⟩, function_heatSourcePath]
    rfl
  have hder := hd.congr_of_eventuallyEq he
  let d (j : Fin 2) : WeaklySingular.Path (Jet 1) T :=
    directionalPath 1 (Pi.single j 1) T (directionalPath 2 (Pi.single j 1) T q)
  have hj (j : Fin 2) : Continuous (fun s =>
      PlaneHeat.evolution ℝ (PlaneHeat.spatialPartial ℝ j
        (PlaneHeat.spatialPartial ℝ j (sourceValue hT 3 q s))) (ν*(t-s)) x) := by
    have hm : Continuous (fun s : ℝ => (ν*(t-s), WeaklySingular.extendPath (Jet 1) hT (d j) s)) :=
      (continuous_const.mul (continuous_const.sub continuous_id)).prodMk
        (WeaklySingular.continuous_extendPath (Jet 1) hT (d j))
    have hh := (PlaneHeat.appliedHeat_joint_continuous ℝ x).comp hm
    simp only [Function.comp_def, PlaneHeat.appliedHeat_eq] at hh
    change Continuous (fun s => PlaneHeat.evolution ℝ (sourceValue hT 1 (d j) s) (ν*(t-s)) x) at hh
    simpa only [d, sourceValue_twice_directional] using hh
  have hl (j : Fin 2) :
      PlaneHeat.spatialPartial ℝ j (PlaneHeat.spatialPartial ℝ j
        (heatSourceValue hT hν 3 q t)) x =
        ∫ s in 0..t, PlaneHeat.evolution ℝ (PlaneHeat.spatialPartial ℝ j
          (PlaneHeat.spatialPartial ℝ j (sourceValue hT 3 q s))) (ν*(t-s)) x := by
    have heval : heatSourceValue hT hν 3 q t =
        BoundedSpatialJets.function Plane ℝ 3
          (heatSourcePath hT hν 3 q ⟨t, ht.1.le, ht.2.le⟩) := by
      funext y
      simp only [heatSourceValue, sourceValue, WeaklySingular.extendPath,
        projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩]
    rw [heval, spatialPartial_twice_heatSourcePath, function_heatSourcePath]
    change (∫ s in 0..t, PlaneHeat.evolution ℝ (sourceValue hT 1 (d j) s) (ν*(t-s)) x) = _
    simp only [d, sourceValue_twice_directional]
  convert hder using 1
  rw [intervalIntegral.integral_smul, intervalIntegral.integral_finsetSum
    (fun j _ => (hj j).intervalIntegrable 0 t)]
  simp only [smul_eq_mul, hl]

end ForcedComputation.PlaneScalarMild

end

end OAI

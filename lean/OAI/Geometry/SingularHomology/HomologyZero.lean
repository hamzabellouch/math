import OAI.Geometry.SingularHomology.HomologyTransfer

namespace OAI

noncomputable section

open CategoryTheory

namespace Problem340

def realSingularHomologyZeroEquiv (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : RealSingularHomology 0 X ≃ₗ[ℝ] ℝ :=
  (asIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℝ ℝ))).toLinearEquiv

def pointHomologyClass {X : Type} [TopologicalSpace X] (x : X) :
    RealSingularHomology 0 X :=
  realHomologyMap 0 (fun _ : PUnit => x) continuous_const
    ((realSingularHomologyZeroEquiv PUnit).symm 1)

theorem pointHomologyClass_ne_zero {X : Type} [TopologicalSpace X] (x : X) :
    pointHomologyClass x ≠ 0 := by
  have hv : (realSingularHomologyZeroEquiv PUnit).symm 1 ≠ 0 := by
    intro h
    have := congrArg (realSingularHomologyZeroEquiv PUnit) h
    simp only [LinearEquiv.apply_symm_apply, map_zero, one_ne_zero] at this
  have hinj := realHomologyMap_injective_of_retraction 0
    (fun _ : PUnit => x) (fun _ : X => PUnit.unit)
    continuous_const continuous_const (fun _ => rfl)
  intro hzero
  apply hv
  apply hinj
  simpa only [pointHomologyClass, map_zero] using hzero

theorem realHomologyMap_pointHomologyClass {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (f : X → X) (hf : Continuous f) (x : X) :
    realHomologyMap 0 f hf (pointHomologyClass x) = pointHomologyClass x := by
  let s : PUnit → X := fun _ => x
  let hs : Continuous s := continuous_const
  let p := PathConnectedSpace.somePath (f x) x
  let H : ContinuousMap.Homotopy
      (continuousMapOf (f ∘ s) (hf.comp hs)) (continuousMapOf s hs) :=
    { toFun := fun tx => p tx.1
      continuous_toFun := p.continuous.comp continuous_fst
      map_zero_left := fun _ => p.source
      map_one_left := fun _ => p.target }
  have heq := realHomologyMap_eq_of_homotopy 0 (hf.comp hs) hs H
  have hmap := (realHomologyMap_comp 0 s f hs hf).symm.trans heq
  exact congrArg (fun A => A ((realSingularHomologyZeroEquiv PUnit).symm 1)) hmap

theorem exists_realHomology_eigenvector_one {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (f : X → X) (hf : Continuous f) :
    ∃ v : RealSingularHomology 0 X, v ≠ 0 ∧ realHomologyMap 0 f hf v = (1 : ℝ) • v := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  exact ⟨pointHomologyClass x, pointHomologyClass_ne_zero x,
    by simpa only [one_smul] using realHomologyMap_pointHomologyClass f hf x⟩

theorem realHomologyMap_zero_eq_id {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (f : X → X) (hf : Continuous f) :
    realHomologyMap 0 f hf = LinearMap.id := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let v := pointHomologyClass x
  let e := realSingularHomologyZeroEquiv X
  have hev : e v ≠ 0 := by
    intro h
    apply pointHomologyClass_ne_zero x
    exact e.injective (by simpa only [map_zero] using h)
  ext u
  have hu : (e u / e v) • v = u := by
    apply e.injective
    simp only [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ (e u) hev
  change realHomologyMap 0 f hf u = u
  calc
    realHomologyMap 0 f hf u = realHomologyMap 0 f hf ((e u / e v) • v) :=
      congrArg (realHomologyMap 0 f hf) hu.symm
    _ = (e u / e v) • v := by
      rw [map_smul, realHomologyMap_pointHomologyClass f hf x]
    _ = u := hu

theorem pathConnectedSpace_standardClock : PathConnectedSpace StandardClock := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere
  · rw [← Module.finrank_eq_rank]
    norm_num
  · norm_num

theorem pathConnectedSpace_standardSphere2 : PathConnectedSpace StandardSphere2 := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere
  · rw [← Module.finrank_eq_rank]
    norm_num
  · norm_num

theorem pathConnectedSpace_counterexampleManifold (q : ℕ) :
    PathConnectedSpace (CounterexampleManifold q) := by
  let := pathConnectedSpace_standardClock
  let := pathConnectedSpace_standardSphere2
  infer_instance

theorem counterexampleManifold_homologyZero_eigenvector (q : ℕ)
    (f : CounterexampleManifold q → CounterexampleManifold q) (hf : Continuous f) :
    ∃ v : RealSingularHomology 0 (CounterexampleManifold q), v ≠ 0 ∧
      realHomologyMap 0 f hf v = (1 : ℝ) • v := by
  let := pathConnectedSpace_counterexampleManifold q
  exact exists_realHomology_eigenvector_one f hf

theorem finiteDimensional_realSingularHomologyZero (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : FiniteDimensional ℝ (RealSingularHomology 0 X) :=
  FiniteDimensional.of_injective (realSingularHomologyZeroEquiv X).toLinearMap
    (realSingularHomologyZeroEquiv X).injective

theorem finrank_realSingularHomologyZero (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] : Module.finrank ℝ (RealSingularHomology 0 X) = 1 := by
  rw [(realSingularHomologyZeroEquiv X).finrank_eq]
  simp

theorem one_mem_homologyRadiusSet {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (f : X → X) (hf : Continuous f) :
    (1 : ℝ) ∈ {r : ℝ | ∃ n : ℕ, ∃ a b : ℝ, ∃ u v : RealSingularHomology n X,
      (u ≠ 0 ∨ v ≠ 0) ∧
      realHomologyMap n f hf u = a • u - b • v ∧
      realHomologyMap n f hf v = b • u + a • v ∧
      r = Real.sqrt (a ^ 2 + b ^ 2)} := by
  obtain ⟨v, hv, heig⟩ := exists_realHomology_eigenvector_one f hf
  refine ⟨0, 1, 0, v, 0, Or.inl hv, ?_, ?_, ?_⟩
  · simpa only [zero_smul, sub_zero] using heig
  · simp
  · norm_num

end Problem340

end

end OAI

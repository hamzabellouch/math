import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarCompactBridge

namespace OAI

/-! Periodicity and zero mean for the planar torus interpretation of the
Hamiltonian, with integration over its unit-square fundamental domain. -/

noncomputable section
namespace ForcedComputation
open ShearFlows PlanarHamiltonian Set MeasureTheory Filter
open scoped BigOperators ContDiff Topology

def PlanePeriodic {E : Type*} (f : Plane → E) : Prop :=
  ∀ (x : Plane) (n : Fin 2 → ℤ), f (x + fun j => (n j : ℝ)) = f x

theorem plane_opposite_faces (j : Fin 2) (x : Fin 1 → ℝ) :
    j.insertNth 1 x = j.insertNth 0 x + fun k => ((Pi.single j 1 : Fin 2 → ℤ) k : ℝ) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨k, rfl⟩
  · simp
  · simp [Fin.succAbove_ne]

theorem integral_planar_periodic_derivative {g : Plane → ℝ}
    (hg : ContDiff ℝ ∞ g) (hp : PlanePeriodic g) (j : Fin 2) :
    (∫ x in Icc (0 : Plane) (fun _ => 1), fderiv ℝ g x (PlanarHamiltonian.basis j)) = 0 := by
  let F : Fin 2 → Plane → ℝ := fun k => if k = j then g else fun _ => 0
  let F' : Fin 2 → Plane → Plane →L[ℝ] ℝ := fun k x => if k = j then fderiv ℝ g x else 0
  have he (x : Plane) : (∑ k, F' k x (Pi.single k 1)) =
      fderiv ℝ g x (PlanarHamiltonian.basis j) := by
    simp [F', PlanarHamiltonian.basis, apply_ite, ite_apply]
  have hc : ∀ k, ContinuousOn (F k) (Icc (0 : Plane) (fun _ => 1)) := by
    intro k
    by_cases hk : k = j <;> simp only [F, hk, ite_true, ite_false]
    · exact hg.continuous.continuousOn
    · exact continuousOn_const
  have hd : ∀ x : Plane, ∀ k, HasFDerivAt (F k) (F' k x) x := by
    intro x k
    by_cases hk : k = j <;> simp only [F, F', hk, ite_true, ite_false]
    · exact (hg.differentiable (by simp) x).hasFDerivAt
    · exact hasFDerivAt_const _ _
  have hi : IntegrableOn (fun x => ∑ k, F' k x (Pi.single k 1))
      (Icc (0 : Plane) (fun _ => 1)) := by
    simp_rw [he]
    exact ((hg.continuous_fderiv (by simp)).clm_apply continuous_const).integrableOn_Icc
  have ht := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Plane) (fun _ => 1) (fun _ => by norm_num) F F' ∅ countable_empty hc
    (fun x _ k => hd x k) hi
  simp only [he] at ht
  rw [ht]
  apply Finset.sum_eq_zero
  intro k _
  have hf (x : Fin 1 → ℝ) : F k (k.insertNth 1 x) = F k (k.insertNth 0 x) := by
    by_cases hk : k = j
    · simp only [F, hk, ite_true]
      rw [plane_opposite_faces]
      exact hp _ _
    · simp [F, hk]
  simp only [Pi.zero_apply, hf, sub_self]

theorem planar_field_mean_zero {H : Plane → ℝ}
    (hH : ContDiff ℝ ∞ H) (hp : PlanePeriodic H) :
    (∫ x in Icc (0 : Plane) (fun _ => 1), field H x) = 0 := by
  have hi : IntegrableOn (field H) (Icc (0 : Plane) (fun _ => 1)) :=
    (field_smooth hH).continuous.integrableOn_Icc
  ext j
  change (ContinuousLinearMap.proj j : Plane →L[ℝ] ℝ)
    (∫ x in Icc (0 : Plane) (fun _ => 1), field H x) = 0
  rw [← (ContinuousLinearMap.proj j : Plane →L[ℝ] ℝ).integral_comp_comm hi]
  fin_cases j
  · have he : (fun x => field H x 0) = spatialD 1 H := by
      funext x
      simp [field]
    change (∫ x in Icc (0 : Plane) (fun _ => 1), field H x 0) = 0
    rw [he]
    exact integral_planar_periodic_derivative hH hp 1
  · have he : (fun x => field H x 1) = fun x => -spatialD 0 H x := by
      funext x
      simp [field]
    change (∫ x in Icc (0 : Plane) (fun _ => 1), field H x 1) = 0
    rw [he]
    rw [integral_neg]
    change -(∫ x in Icc (0 : Plane) (fun _ => 1), fderiv ℝ H x (PlanarHamiltonian.basis 0)) = 0
    rw [integral_planar_periodic_derivative hH hp 0, neg_zero]

theorem planar_field_periodic {H : Plane → ℝ}
    (hH : ContDiff ℝ ∞ H) (hp : PlanePeriodic H) : PlanePeriodic (field H) := by
  intro x n
  have he := fderiv_translation (hH.differentiable (by simp)) (fun y => hp y n) x
  simp only [field, spatialD, he]

theorem planar_slice_potential_smooth {H : FieldExpr} (hH : H.Valid) (s : ℝ) :
    ContDiff ℝ ∞ (fun x : Plane => SpatialExpression.spatialValue H (atHeight x s)) := by
  have hi : ContDiff ℝ ∞ (fun x : Plane => atHeight x s) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · change ContDiff ℝ ∞ (fun x : Plane => x 0)
      exact contDiff_apply ℝ ℝ 0
    · change ContDiff ℝ ∞ (fun x : Plane => x 1)
      exact contDiff_apply ℝ ℝ 1
    · change ContDiff ℝ ∞ (fun _ : Plane => s)
      exact contDiff_const
  have h := (SpatialExpression.spatialValue_smooth hH).comp hi
  exact h

theorem planar_slice_potential_periodic {H : FieldExpr}
    (hp : CubePeriodic 1 (SpatialExpression.spatialValue H)) (s : ℝ) :
    PlanePeriodic (fun x => SpatialExpression.spatialValue H (atHeight x s)) := by
  intro x n
  have he : atHeight (x + fun j => (n j : ℝ)) s =
      atHeight x s + latticeVector 1 ![n 0, n 1, 0] := by
    ext j
    fin_cases j <;> simp [atHeight, latticeVector]
  change SpatialExpression.spatialValue H (atHeight (x + fun j => (n j : ℝ)) s) =
    SpatialExpression.spatialValue H (atHeight x s)
  rw [he]
  exact hp _ _

theorem planarSlice_mean_zero {H : FieldExpr} (hH : H.Valid)
    (hp : CubePeriodic 1 (SpatialExpression.spatialValue H)) (s : ℝ) :
    (∫ x in Icc (0 : Plane) (fun _ => 1), planarSlice H s x) = 0 := by
  exact planar_field_mean_zero (planar_slice_potential_smooth hH s)
    (planar_slice_potential_periodic hp s)

theorem planarSlice_smooth {H : FieldExpr} (hH : H.Valid) (s : ℝ) :
    ContDiff ℝ ∞ (planarSlice H s) :=
  field_smooth (planar_slice_potential_smooth hH s)

theorem planarSlice_divergence {H : FieldExpr} (hH : H.Valid) (s : ℝ) (x : Plane) :
    PlanarHamiltonian.divergence (planarSlice H s) x = 0 :=
  field_divergence (planar_slice_potential_smooth hH s) x

theorem planarSlice_spatial_periodic {H : FieldExpr} (hH : H.Valid)
    (hp : CubePeriodic 1 (SpatialExpression.spatialValue H)) (s : ℝ) :
    PlanePeriodic (planarSlice H s) :=
  planar_field_periodic (planar_slice_potential_smooth hH s)
    (planar_slice_potential_periodic hp s)

theorem processor_slice_zero {n : ℕ} (p : Fin n → Pulse) (s : ℝ)
    (hp : ∀ i, (PeriodicExpr.intervalPulse (p i).start (p i).finish).val s = 0) :
    planarSlice (processorExpression p) s = 0 := by
  have he : (fun x => SpatialExpression.spatialValue (processorExpression p) (atHeight x s)) =
      (fun _ : Plane => (0 : ℝ)) := by
    funext x
    unfold SpatialExpression.spatialValue processorExpression
    rw [FieldExpr.val_sum]
    simp only [List.map_ofFn, List.sum_ofFn]
    apply Finset.sum_eq_zero
    intro i _
    change (PeriodicExpr.intervalPulse (p i).start (p i).finish).val s *
      (p i).spatialExpression.val (0, atHeight x s) = 0
    rw [hp i, zero_mul]
  unfold planarSlice
  rw [he]
  ext j
  simp [field, spatialD]

theorem normalized_planar_zero_near_zero (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x, planarSlice (Recorder.Planar.normalizedHamiltonian I hI) s x = 0 := by
  have he : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i,
      (PeriodicExpr.intervalPulse (Recorder.Planar.normalizedPulse I hI i).start
        (Recorder.Planar.normalizedPulse I hI i).finish).val s = 0 :=
    eventually_all.mpr (fun i => periodicPulse_zero_near_zero
      (Recorder.Planar.normalizedPulse_valid I hI i) (Recorder.Planar.normalizedPulse_inUnit I hI i))
  filter_upwards [he] with s hs
  intro x
  exact congrFun (processor_slice_zero (Recorder.Planar.normalizedPulse I hI) s hs) x

end ForcedComputation

end

end OAI

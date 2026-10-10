import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Masks
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Pulses

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

theorem transverseSum_smooth {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Space →L[ℝ] E) (f : ι → E → ℝ) (v : ι → Space)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) : ContDiff ℝ ∞ (transverseSum P f v) := by
  apply ContDiff.sum
  intro i _
  exact ((hf i).comp P.contDiff).smul contDiff_const

theorem sevenFields_smooth {n : ℕ}
    (p q : Fin n → Plane) (lam z : Fin n → ℝ) (z₀ : ℝ)
    (Am Ap : Fin n → Plane → ℝ) (Z gx gy : Fin n → ℝ → ℝ)
    (hAm : ∀ i, ContDiff ℝ ∞ (Am i)) (hAp : ∀ i, ContDiff ℝ ∞ (Ap i))
    (hZ : ∀ i, ContDiff ℝ ∞ (Z i)) (hgx : ∀ i, ContDiff ℝ ∞ (gx i))
    (hgy : ∀ i, ContDiff ℝ ∞ (gy i)) :
    ∀ j, ContDiff ℝ ∞ (sevenFields p q lam z z₀ Am Ap Z gx gy j) := by
  have hx : ContDiff ℝ ∞ (fun X : Plane => X 0) :=
    (ContinuousLinearMap.proj 0 : Plane →L[ℝ] ℝ).contDiff
  have hy : ContDiff ℝ ∞ (fun X : Plane => X 1) :=
    (ContinuousLinearMap.proj 1 : Plane →L[ℝ] ℝ).contDiff
  intro j
  fin_cases j <;> simp only [sevenFields] <;> try dsimp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.zero_eta]
  · exact transverseSum_smooth _ _ _ (fun i => contDiff_const.mul (hAm i))
  · exact transverseSum_smooth _ _ _ (fun i =>
      (contDiff_const.mul ((hZ i).comp hy)).mul ((hgx i).comp hx))
  · exact transverseSum_smooth _ _ _ (fun i =>
      (contDiff_const.mul ((hZ i).comp hy)).mul ((hgy i).comp hx))
  · exact transverseSum_smooth _ _ _ (fun i => ((hZ i).comp hy).mul ((hgx i).comp hx))
  · exact transverseSum_smooth _ _ _ (fun i =>
      (contDiff_const.mul ((hZ i).comp hy)).mul ((hgy i).comp hx))
  · exact transverseSum_smooth _ _ _ hZ
  · exact transverseSum_smooth _ _ _ (fun i => contDiff_const.mul (hAp i))

def CubePeriodic {E : Type*} (L : ℝ) (W : Space → E) : Prop :=
  ∀ x n, W (x + latticeVector L n) = W x

theorem circle_periodic_mul_int {E : Type*} {f : ℝ → E} {L : ℝ}
    (h : Function.Periodic f L) (s : ℝ) (n : ℤ) : f (s + L * (n : ℝ)) = f s := by
  simpa [mul_comm] using h.int_mul n s

theorem selectTwo_apply (j k : Fin 3) (x : Space) : selectTwo j k x = ![x j, x k] := by
  ext a
  fin_cases a <;> simp [selectTwo]

theorem selectTwo_zero_one (x : Space) : selectTwo 0 1 x = horizontal x :=
  selectTwo_apply 0 1 x

theorem sevenFields_periodic {n : ℕ}
    (p q : Fin n → Plane) (lam z : Fin n → ℝ) (z₀ L : ℝ)
    (Am Ap : Fin n → Plane → ℝ) (Z gx gy : Fin n → ℝ → ℝ)
    (hAm : ∀ i X (m : Fin 2 → ℤ), Am i (X + fun k => L * ((m k : ℤ) : ℝ)) = Am i X)
    (hAp : ∀ i X (m : Fin 2 → ℤ), Ap i (X + fun k => L * ((m k : ℤ) : ℝ)) = Ap i X)
    (hZ : ∀ i, Function.Periodic (Z i) L) (hgx : ∀ i, Function.Periodic (gx i) L)
    (hgy : ∀ i, Function.Periodic (gy i) L) :
    ∀ j, CubePeriodic L (sevenFields p q lam z z₀ Am Ap Z gx gy j) := by
  intro j x m
  have hxy : selectTwo 0 1 (x + latticeVector L m) =
      selectTwo 0 1 x + fun k => L * ((![(m 0),(m 1)] k : ℤ) : ℝ) := by
    ext k
    fin_cases k <;> simp [selectTwo, latticeVector]
  have hAm' (i) : Am i (selectTwo 0 1 (x + latticeVector L m)) =
      Am i (selectTwo 0 1 x) := by
    rw [hxy]
    exact hAm i (selectTwo 0 1 x) ![m 0,m 1]
  have hAp' (i) : Ap i (selectTwo 0 1 (x + latticeVector L m)) =
      Ap i (selectTwo 0 1 x) := by
    rw [hxy]
    exact hAp i (selectTwo 0 1 x) ![m 0,m 1]
  have hZ' (i) (k : Fin 3) : Z i ((x + latticeVector L m) k) = Z i (x k) :=
    circle_periodic_mul_int (hZ i) _ _
  have hgx' (i) (k : Fin 3) : gx i ((x + latticeVector L m) k) = gx i (x k) :=
    circle_periodic_mul_int (hgx i) _ _
  have hgy' (i) (k : Fin 3) : gy i ((x + latticeVector L m) k) = gy i (x k) :=
    circle_periodic_mul_int (hgy i) _ _
  simp only [selectTwo_apply, Pi.add_apply] at hAm' hAp' hZ' hgx' hgy'
  fin_cases j <;> simp [sevenFields, transverseSum, hAm', hAp', selectTwo_apply,
    hZ', hgx', hgy']

theorem height_profile_mean_zero (L : ℝ) (Z g : ℝ → ℝ)
    (hZ : (∫ z in Icc (0 : ℝ) L, Z z) = 0) (j : Fin 2) :
    (∫ x in fundamentalCube L, Z (x 2) * g (x j.castSucc)) = 0 := by
  fin_cases j
  · have h := cube_integral_three L g (fun _ => 1) Z
    simpa [hZ, mul_comm] using h
  · have h := cube_integral_three L (fun _ => 1) g Z
    simpa [hZ, mul_comm] using h

theorem height_only_mean_zero (L : ℝ) (Z : ℝ → ℝ)
    (hZ : (∫ z in Icc (0 : ℝ) L, Z z) = 0) :
    (∫ x in fundamentalCube L, Z (x 2)) = 0 := by
  simpa using height_profile_mean_zero L Z (fun _ => 1) hZ 0

theorem transverseSum_mean_zero {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Space →L[ℝ] E) (f : ι → E → ℝ) (v : ι → Space) (L : ℝ)
    (hc : ∀ i, Continuous (f i)) (hz : ∀ i, (∫ x in fundamentalCube L, f i (P x)) = 0) :
    (∫ x in fundamentalCube L, transverseSum P f v x) = 0 := by
  unfold transverseSum
  rw [integral_finsetSum]
  · simp [integral_smul_const, hz]
  · intro i _
    exact (((hc i).comp P.continuous).smul continuous_const).integrableOn_Icc

theorem sevenFields_mean_zero {n : ℕ}
    (p q : Fin n → Plane) (lam z : Fin n → ℝ) (z₀ L : ℝ)
    (Am Ap : Fin n → Plane → ℝ) (Z gx gy : Fin n → ℝ → ℝ)
    (hAm : ∀ i, Continuous (Am i)) (hAp : ∀ i, Continuous (Ap i))
    (hZ : ∀ i, Continuous (Z i)) (hgx : ∀ i, Continuous (gx i))
    (hgy : ∀ i, Continuous (gy i))
    (hmAm : ∀ i, (∫ x in fundamentalCube L, Am i (horizontal x)) = 0)
    (hmAp : ∀ i, (∫ x in fundamentalCube L, Ap i (horizontal x)) = 0)
    (hmZ : ∀ i, (∫ s in Icc (0 : ℝ) L, Z i s) = 0) :
    ∀ j, (∫ x in fundamentalCube L, sevenFields p q lam z z₀ Am Ap Z gx gy j x) = 0 := by
  have hx : Continuous (fun X : Plane => X 0) := continuous_apply 0
  have hy : Continuous (fun X : Plane => X 1) := continuous_apply 1
  intro j
  fin_cases j <;> simp only [sevenFields] <;> try dsimp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.zero_eta]
  · apply transverseSum_mean_zero _ _ _ L (fun i => (hAm i).const_mul _)
    intro i
    simp [selectTwo_zero_one, integral_const_mul, hmAm]
  · apply transverseSum_mean_zero _ _ _ L (fun i =>
      (((hZ i).comp hy).const_mul _).mul ((hgx i).comp hx))
    intro i
    change (∫ x in fundamentalCube L, (-lam i) * Z i (x 2) * gx i (x 0)) = 0
    simp only [mul_assoc, integral_const_mul]
    rw [show (∫ a : Space in fundamentalCube L, Z i (a 2) * gx i (a 0)) = 0 from
      height_profile_mean_zero L (Z i) (gx i) (hmZ i) 0, mul_zero]
  · apply transverseSum_mean_zero _ _ _ L (fun i =>
      (((hZ i).comp hy).const_mul _).mul ((hgy i).comp hx))
    intro i
    change (∫ x in fundamentalCube L, ((lam i)⁻¹ - 1) * Z i (x 2) * gy i (x 1)) = 0
    simp only [mul_assoc, integral_const_mul]
    rw [show (∫ a : Space in fundamentalCube L, Z i (a 2) * gy i (a 1)) = 0 from
      height_profile_mean_zero L (Z i) (gy i) (hmZ i) 1, mul_zero]
  · apply transverseSum_mean_zero _ _ _ L (fun i => ((hZ i).comp hy).mul ((hgx i).comp hx))
    intro i
    exact height_profile_mean_zero L (Z i) (gx i) (hmZ i) 0
  · apply transverseSum_mean_zero _ _ _ L (fun i =>
      (((hZ i).comp hy).const_mul _).mul ((hgy i).comp hx))
    intro i
    change (∫ x in fundamentalCube L, (lam i - 1) * Z i (x 2) * gy i (x 1)) = 0
    simp only [mul_assoc, integral_const_mul]
    rw [show (∫ a : Space in fundamentalCube L, Z i (a 2) * gy i (a 1)) = 0 from
      height_profile_mean_zero L (Z i) (gy i) (hmZ i) 1, mul_zero]
  · apply transverseSum_mean_zero _ _ _ L hZ
    intro i
    exact height_only_mean_zero L (Z i) (hmZ i)
  · apply transverseSum_mean_zero _ _ _ L (fun i => (hAp i).const_mul _)
    intro i
    simp [selectTwo_zero_one, integral_const_mul, hmAp]

namespace Input

def spatialFields (d : Input) : Fin 7 → Space → Space :=
  letI := neZeroTwo
  sevenFields (fun i => (d.sources i).center) (fun i => (d.targets i).center)
    (fun i => (d.instructions.get i).factor) (fun i => d.privateHeight i) d.codingHeight
    d.sourceMask d.targetMask d.heightMask
    (fun i => d.horizontalProfile i 0) (fun i => d.horizontalProfile i 1)

def realizingVelocity (d : Input) : Velocity := pulsedSum periodPulse d.spatialFields

end Input

theorem spatialFields_smooth {d : Input} (hd : ValidInput d) :
    ∀ j, ContDiff ℝ ∞ (d.spatialFields j) :=
  sevenFields_smooth _ _ _ _ _ _ _ _ _ _ (sourceMask_smooth hd) (targetMask_smooth hd)
    (heightMask_smooth hd) (fun i => horizontalProfile_smooth hd i 0)
    (fun i => horizontalProfile_smooth hd i 1)

theorem spatialFields_periodic (d : Input) :
    ∀ j, CubePeriodic d.period (d.spatialFields j) :=
  sevenFields_periodic _ _ _ _ _ _ _ _ _ _ _
    (fun i X m => planarMask_periodic d.period (d.sources i) d.sourceRadius X m)
    (fun i X m => planarMask_periodic d.period (d.targets i) d.targetRadius X m)
    (heightMask_periodic d) (fun i => horizontalProfile_periodic d i 0)
    (fun i => horizontalProfile_periodic d i 1)

theorem spatialFields_divergence_advection {d : Input} (hd : ValidInput d) :
    ∀ j x, divergence (d.spatialFields j) x = 0 ∧ advection (d.spatialFields j) x = 0 :=
  sevenFields_divergence_advection _ _ _ _ _ _ _ _ _ _
    (fun i => (sourceMask_smooth hd i).differentiable (by simp))
    (fun i => (targetMask_smooth hd i).differentiable (by simp))
    (fun i => (heightMask_smooth hd i).differentiable (by simp))
    (fun i => (horizontalProfile_smooth hd i 0).differentiable (by simp))
    (fun i => (horizontalProfile_smooth hd i 1).differentiable (by simp))

theorem spatialFields_mean_zero {d : Input} (hd : ValidInput d) :
    ∀ j, (∫ x in fundamentalCube d.period, d.spatialFields j x) = 0 :=
  sevenFields_mean_zero _ _ _ _ _ _ _ _ _ _ _
    (fun i => (sourceMask_smooth hd i).continuous)
    (fun i => (targetMask_smooth hd i).continuous)
    (fun i => (heightMask_smooth hd i).continuous)
    (fun i => (horizontalProfile_smooth hd i 0).continuous)
    (fun i => (horizontalProfile_smooth hd i 1).continuous)
    (fun i => planarMask_cube_mean_zero (by exact_mod_cast hd.period_pos) _ (sourceRadius_pos hd))
    (fun i => planarMask_cube_mean_zero (by exact_mod_cast hd.period_pos) _ (targetRadius_pos hd))
    (heightMask_integral_zero hd)

theorem realizingVelocity_smooth {d : Input} (hd : ValidInput d) :
    ContDiff ℝ ∞ d.realizingVelocity :=
  pulsedSum_smooth periodPulse d.spatialFields periodPulse_smooth (spatialFields_smooth hd)

theorem realizingVelocity_spatially_periodic (d : Input) :
    SpatiallyPeriodic d.period d.realizingVelocity := by
  intro t x n
  simp only [Input.realizingVelocity, pulsedSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [spatialFields_periodic d j x n]

theorem realizingVelocity_time_periodic (d : Input) : TimePeriodic d.realizingVelocity := by
  intro t x
  simp only [Input.realizingVelocity, pulsedSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [periodPulse_periodic j t]

theorem realizingVelocity_divergence_advection {d : Input} (hd : ValidInput d) :
    Solenoidal d.realizingVelocity ∧ ZeroAdvection d.realizingVelocity :=
  pulsedSum_divergence_advection periodPulse d.spatialFields periodPulses_separated
    (fun j => (spatialFields_smooth hd j).differentiable (by simp))
    (fun j x => (spatialFields_divergence_advection hd j x).1)
    (fun j x => (spatialFields_divergence_advection hd j x).2)

theorem realizingVelocity_mean_zero {d : Input} (hd : ValidInput d) :
    HasZeroMean d.period d.realizingVelocity :=
  pulsedSum_mean_zero periodPulse d.spatialFields d.period
    (fun j => (spatialFields_smooth hd j).continuous) (spatialFields_mean_zero hd)

theorem realizingVelocity_vanish_near_integers (d : Input) (k : ℤ) {t : ℝ}
    (ht : |t - (k : ℝ)| < (1 / 32 : ℝ)) (x : Space) : d.realizingVelocity (t,x) = 0 := by
  simp [Input.realizingVelocity, pulsedSum, periodPulses_vanish_near_integers k ht]

theorem realizingVelocity_gaps (d : Input) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hg : ∀ j, t ∉ Ioo (stageStart j : ℝ) (stageFinish j : ℝ)) (x : Space) :
    d.realizingVelocity (t,x) = 0 := by
  have hz (j) : periodPulse j t = 0 := by
    rw [periodPulse_eq_on_period j ht]
    by_contra hj
    exact hg j (smoothPulse_support (by exact_mod_cast (stage_intervals j).2.1) hj)
  simp [Input.realizingVelocity, pulsedSum, hz]

theorem realizingVelocity_empty (d : Input) (he : d.instructions = []) :
    d.realizingVelocity = 0 := by
  have : IsEmpty (Fin d.instructions.length) := by simp [he]
  funext tx
  change (∑ j, periodPulse j tx.1 • d.spatialFields j tx.2) = 0
  apply Finset.sum_eq_zero
  intro j _
  have hj : d.spatialFields j tx.2 = 0 := by fin_cases j <;> simp [Input.spatialFields, sevenFields, transverseSum]
  simp [hj]

end ShearFlows

end

end OAI

import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EnergyCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

theorem derivative_sub {U V : Space → Space}
    (hU : Differentiable ℝ U) (hV : Differentiable ℝ V) (j : Fin 3) :
    derivative (fun y => U y - V y) j = fun y => derivative U j y - derivative V j y := by
  funext x
  simp only [derivative, fderiv_fun_sub (hU x) (hV x), sub_apply]

theorem laplacian_sub {U V : Space → Space}
    (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V) (x : Space) :
    laplacian (fun y => U y - V y) x = laplacian U x - laplacian V x := by
  simp only [laplacian, derivative_sub (hU.differentiable (by norm_num))
    (hV.differentiable (by norm_num))]
  simp only [fderiv_fun_sub ((derivative_contDiff hU _).differentiable (by norm_num) x)
    ((derivative_contDiff hV _).differentiable (by norm_num) x), sub_apply,
    Finset.sum_sub_distrib]

theorem advection_sub {U V : Space → Space}
    (hU : Differentiable ℝ U) (hV : Differentiable ℝ V) (x : Space) :
    advection U x - advection V x =
      fderiv ℝ (fun y => U y - V y) x (U x) + fderiv ℝ V x (U x - V x) := by
  simp only [advection, fderiv_fun_sub (hU x) (hV x), sub_apply, map_sub]
  abel

theorem laplacian_continuous {U : Space → Space} (hU : ContDiff ℝ 2 U) :
    Continuous (laplacian U) := continuous_finsetSum _ (fun j _ =>
  ((derivative_contDiff hU j).continuous_fderiv (by norm_num)).clm_apply continuous_const)

theorem gradient_continuous {p : Space → ℝ} (hp : ContDiff ℝ 1 p) :
    Continuous (gradient p) := continuous_pi (fun coordinate =>
  (hp.continuous_fderiv (by norm_num)).clm_apply
    (show Continuous (fun _ : Space => basis coordinate) from continuous_const))

theorem initialTimeDerivative_sub {u v : Velocity} {t : ℝ} {x : Space}
    (hu : DifferentiableWithinAt ℝ (fun s => u (s,x)) (Ici 0) t)
    (hv : DifferentiableWithinAt ℝ (fun s => v (s,x)) (Ici 0) t) :
    initialTimeDerivative (fun y => u y - v y) t x =
      initialTimeDerivative u t x - initialTimeDerivative v t x :=
  derivWithin_sub hu hv

theorem classical_difference_equation {L ν : ℝ} {f u v : Velocity} {p : Pressure}
    (hu : IsClassicalSolution L ν f u p) (hv : IsClassicalSolution L ν f v (fun _ => 0))
    {t : ℝ} (ht : 0 ≤ t) (x : Space) :
    initialTimeDerivative (fun y => u y - v y) t x =
      -gradient (fun y => p (t,y)) x + ν • laplacian (fun y => u (t,y) - v (t,y)) x -
        fderiv ℝ (fun y => u (t,y) - v (t,y)) x (u (t,x)) -
        fderiv ℝ (fun y => v (t,y)) x (u (t,x) - v (t,x)) := by
  have hU := hu.regularity.spatial_u t ht
  have hV := hv.regularity.spatial_u t ht
  rw [initialTimeDerivative_sub (hu.regularity.temporal_u t ht x)
    (hv.regularity.temporal_u t ht x), laplacian_sub hU hV, smul_sub]
  have hvEq := hv.equation t ht x
  have hzero : gradient (fun _ : Space => (0 : ℝ)) x = 0 := by
    ext j
    simp [gradient]
  rw [hzero, neg_zero, zero_add] at hvEq
  have hadv := advection_sub (hU.differentiable (by norm_num))
    (hV.differentiable (by norm_num)) x
  have hdiff := congrArg₂ (· - ·) (hu.equation t ht x) hvEq
  rw [← sub_add_sub_comm, hadv] at hdiff
  linear_combination hdiff

theorem integrated_comparison_inequality {L ν B : ℝ} (hL : 0 ≤ L) (hν : 0 ≤ ν)
    {W U V G : Space → Space} {p : Space → ℝ}
    (hW : ContDiff ℝ 2 W) (hU : ContDiff ℝ 1 U) (hV : ContDiff ℝ 1 V)
    (hp : ContDiff ℝ 1 p) (hWp : CubePeriodic L W) (hUp : CubePeriodic L U)
    (hpp : CubePeriodic L p) (hdivW : ∀ x, divergence W x = 0)
    (hdivU : ∀ x, divergence U x = 0) (hB : ∀ x, ‖fderiv ℝ V x‖ ≤ B)
    (heq : ∀ x, G x = -gradient p x + ν • laplacian W x -
      fderiv ℝ W x (U x) - fderiv ℝ V x (W x)) :
    (∫ x in fundamentalCube L, dot (W x) (G x)) ≤
      3 * B * ∫ x in fundamentalCube L, dot (W x) (W x) := by
  have hWi : IntegrableOn (fun x => dot (W x) (W x)) (fundamentalCube L) :=
    (dot_continuous hW.continuous hW.continuous).integrableOn_Icc
  have hPi : IntegrableOn (fun x => dot (W x) (gradient p x)) (fundamentalCube L) :=
    (dot_continuous hW.continuous (gradient_continuous hp)).integrableOn_Icc
  have hLi : IntegrableOn (fun x => dot (W x) (laplacian W x)) (fundamentalCube L) :=
    (dot_continuous hW.continuous (laplacian_continuous hW)).integrableOn_Icc
  have hTi : IntegrableOn (fun x => dot (W x) (fderiv ℝ W x (U x))) (fundamentalCube L) :=
    (dot_continuous hW.continuous
      ((hW.continuous_fderiv (by norm_num)).clm_apply hU.continuous)).integrableOn_Icc
  have hVi : IntegrableOn (fun x => dot (W x) (fderiv ℝ V x (W x))) (fundamentalCube L) :=
    (dot_continuous hW.continuous
      ((hV.continuous_fderiv (by norm_num)).clm_apply hW.continuous)).integrableOn_Icc
  have hpress := integral_pressure_transport_zero hL (hW.of_le (by norm_num)) hp hWp hpp hdivW
  have htrans := integral_transport_zero hL (hW.of_le (by norm_num)) hU hWp hUp hdivU
  have hlap := integral_dot_laplacian_nonpos hL hW hWp
  have hlin : -(∫ x in fundamentalCube L, dot (W x) (fderiv ℝ V x (W x))) ≤
      3 * B * ∫ x in fundamentalCube L, dot (W x) (W x) := by
    rw [← integral_neg, ← integral_const_mul]
    apply integral_mono hVi.neg (hWi.const_mul _)
    intro x
    calc
      -dot (W x) (fderiv ℝ V x (W x)) ≤ |dot (W x) (fderiv ℝ V x (W x))| := neg_le_abs _
      _ ≤ 3 * ‖fderiv ℝ V x‖ * dot (W x) (W x) := dot_linear_bound _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hB x) (by norm_num)) (dot_self_nonneg _)
  have hi1 : IntegrableOn (fun x => -dot (W x) (gradient p x) +
      ν * dot (W x) (laplacian W x)) (fundamentalCube L) := hPi.neg.add (hLi.const_mul ν)
  have hi2 : IntegrableOn (fun x => -dot (W x) (gradient p x) +
      ν * dot (W x) (laplacian W x) - dot (W x) (fderiv ℝ W x (U x)))
      (fundamentalCube L) := hi1.sub hTi
  simp only [heq, dot_sub_right, dot_add_right, dot_neg_right, dot_smul_right]
  rw [integral_sub hi2 hVi, integral_sub hi1 hTi,
    integral_add (μ := volume.restrict (fundamentalCube L))
      (f := fun x => -dot (W x) (gradient p x))
      (g := fun x => ν * dot (W x) (laplacian W x)) hPi.neg (hLi.const_mul ν), integral_neg, integral_const_mul, hpress, htrans]
  have hh := mul_nonpos_of_nonneg_of_nonpos hν hlap
  linarith

end ShearFlows

end

end OAI

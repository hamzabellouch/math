import OAI.MathematicalPhysics.NavierStokes.ShearFlows.ForceIdentities

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

def dot (a b : Space) : ℝ := ∑ j, a j * b j

theorem dot_comm (a b : Space) : dot a b = dot b a := by
  simp only [dot, mul_comm]

@[simp] theorem dot_zero_right (a : Space) : dot a 0 = 0 := by simp [dot]
@[simp] theorem dot_zero_left (a : Space) : dot 0 a = 0 := by simp [dot]
@[simp] theorem dot_add_right (a b c : Space) : dot a (b+c) = dot a b + dot a c := by
  simp [dot, mul_add, Finset.sum_add_distrib]
@[simp] theorem dot_sub_right (a b c : Space) : dot a (b-c) = dot a b - dot a c := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]
@[simp] theorem dot_neg_right (a b : Space) : dot a (-b) = - dot a b := by simp [dot]
@[simp] theorem dot_smul_right (a b : Space) (c : ℝ) : dot a (c • b) = c * dot a b := by
  simp [dot, Finset.mul_sum, mul_left_comm]

theorem dot_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → Space} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (fun x => dot (f x) (g x)) := by
  exact ContDiff.sum (fun j _ => ((contDiff_pi.mp hf) j).mul ((contDiff_pi.mp hg) j))

theorem dot_continuous {E : Type*} [TopologicalSpace E] {f g : E → Space}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => dot (f x) (g x)) := by
  exact continuous_finsetSum _ (fun j _ => (continuous_apply j |>.comp hf).mul
    (continuous_apply j |>.comp hg))

theorem dot_self_nonneg (a : Space) : 0 ≤ dot a a :=
  Finset.sum_nonneg (fun coordinate _ => mul_self_nonneg (a coordinate))

theorem fderiv_dot {f g : Space → Space} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (x v : Space) :
    fderiv ℝ (fun y => dot (f y) (g y)) x v =
      dot (f x) (fderiv ℝ g x v) + dot (g x) (fderiv ℝ f x v) := by
  unfold dot
  rw [fderiv_fun_sum (A := fun j y => f y j * g y j) (fun j _ => (differentiableAt_pi.mp (hf x) j).mul
    (differentiableAt_pi.mp (hg x) j))]
  simp only [sum_apply]
  simp_rw [fderiv_fun_mul (differentiableAt_pi.mp (hf x) _) (differentiableAt_pi.mp (hg x) _),
    add_apply, smul_apply, smul_eq_mul, fderiv_coordinate hf,
    fderiv_coordinate hg, Finset.sum_add_distrib]

theorem fderiv_dot_self {f : Space → Space} (hf : Differentiable ℝ f) (x v : Space) :
    fderiv ℝ (fun y => dot (f y) (f y)) x v = 2 * dot (f x) (fderiv ℝ f x v) := by
  rw [fderiv_dot hf hf]
  ring

theorem divergence_scalar_mul {g : Space → ℝ} {U : Space → Space}
    (hg : Differentiable ℝ g) (hU : Differentiable ℝ U) (x : Space) :
    divergence (fun y => g y • U y) x = g x * divergence U x + fderiv ℝ g x (U x) := by
  simp only [divergence, derivative, fderiv_fun_smul (hg x) (hU x), add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum, coordinate_trace]

theorem integral_periodic_divergence {L : ℝ} (hL : 0 ≤ L) {U : Space → Space}
    (hU : ContDiff ℝ 1 U) (hperiod : CubePeriodic L U) :
    (∫ x in fundamentalCube L, divergence U x) = 0 := by
  let F : Fin 3 → Space → ℝ := fun j x => U x j
  let F' : Fin 3 → Space → Space →L[ℝ] ℝ := fun j x =>
    (ContinuousLinearMap.proj j).comp (fderiv ℝ U x)
  have he (x : Space) : ∑ j, F' j x (Pi.single j 1) = divergence U x := rfl
  have hd (x : Space) (j : Fin 3) : HasFDerivAt (F j) (F' j x) x :=
    (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x
      ((hU.differentiable (by norm_num)) x).hasFDerivAt
  have hc (j : Fin 3) : Continuous (F j) := (continuous_apply j).comp hU.continuous
  have hdiv : Continuous (divergence U) := continuous_finsetSum _ (fun j _ =>
    (continuous_apply j).comp ((hU.continuous_fderiv (by norm_num)).clm_apply continuous_const))
  have ht := integral_divergence_of_hasFDerivAt_off_countable'
    (0 : Space) (fun _ => L) (fun _ => hL) F F' ∅ countable_empty (fun j => (hc j).continuousOn)
    (fun x _ j => hd x j) (by simp only [he]; exact hdiv.integrableOn_Icc)
  change (∫ x in Icc (0 : Space) (fun _ => L), divergence U x) = 0
  simp only [he] at ht
  rw [ht]
  apply Finset.sum_eq_zero
  intro j _
  have hh (x : Fin 2 → ℝ) : F j (j.insertNth L x) = F j (j.insertNth 0 x) := by
    dsimp [F]
    rw [opposite_faces_translate, hperiod]
  simp only [Pi.zero_apply, hh, sub_self]

theorem integral_pressure_transport_zero {L : ℝ} (hL : 0 ≤ L)
    {W : Space → Space} {p : Space → ℝ} (hW : ContDiff ℝ 1 W) (hp : ContDiff ℝ 1 p)
    (hWp : CubePeriodic L W) (hpp : CubePeriodic L p) (hdiv : ∀ x, divergence W x = 0) :
    (∫ x in fundamentalCube L, dot (W x) (gradient p x)) = 0 := by
  have he (x : Space) : divergence (fun y => p y • W y) x = dot (W x) (gradient p x) := by
    rw [divergence_scalar_mul (hp.differentiable (by norm_num)) (hW.differentiable (by norm_num)),
      hdiv, mul_zero, zero_add]
    exact (coordinate_trace (fderiv ℝ p x) (W x)).symm.trans (by simp only [dot,gradient,mul_comm])
  have hz : (∫ x in fundamentalCube L, divergence (fun y => p y • W y) x) = 0 :=
    integral_periodic_divergence hL (hp.smul hW)
      (fun x n => by rw [hpp, hWp])
  simpa only [he] using hz

theorem integral_transport_zero {L : ℝ} (hL : 0 ≤ L)
    {W U : Space → Space} (hW : ContDiff ℝ 1 W) (hU : ContDiff ℝ 1 U)
    (hWp : CubePeriodic L W) (hUp : CubePeriodic L U) (hdiv : ∀ x, divergence U x = 0) :
    (∫ x in fundamentalCube L, dot (W x) (fderiv ℝ W x (U x))) = 0 := by
  have he (x : Space) : divergence (fun y => dot (W y) (W y) • U y) x =
      2 * dot (W x) (fderiv ℝ W x (U x)) := by
    rw [divergence_scalar_mul ((dot_contDiff hW hW).differentiable (by norm_num))
      (hU.differentiable (by norm_num)), hdiv, mul_zero, zero_add,
      fderiv_dot_self (hW.differentiable (by norm_num))]
  have hz : (∫ x in fundamentalCube L,
      divergence (fun y => dot (W y) (W y) • U y) x) = 0 :=
    integral_periodic_divergence hL ((dot_contDiff hW hW).smul hU)
    (fun x n => by rw [hWp, hUp])
  simp only [he, integral_const_mul] at hz
  linarith

@[simp] theorem dot_sum_right {ι : Type*} (s : Finset ι) (a : Space) (b : ι → Space) :
    dot a (∑ i ∈ s, b i) = ∑ i ∈ s, dot a (b i) := by
  simp only [dot, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem CubePeriodic.fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} {g : Space → E} (hp : CubePeriodic L g) (hg : Differentiable ℝ g) :
    CubePeriodic L (fderiv ℝ g) := by
  intro x n
  exact fderiv_translation hg (fun y => hp y n) x

theorem CubePeriodic.derivative {L : ℝ} {W : Space → Space} (hp : CubePeriodic L W)
    (hW : Differentiable ℝ W) (j : Fin 3) : CubePeriodic L (derivative W j) := by
  intro x n
  unfold ShearFlows.derivative
  rw [hp.fderiv hW x n]

theorem derivative_contDiff {W : Space → Space} (hW : ContDiff ℝ 2 W) (j : Fin 3) :
    ContDiff ℝ 1 (derivative W j) := by
  exact (hW.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const

theorem divergence_dot_derivative {W : Space → Space} (hW : ContDiff ℝ 2 W) (x : Space) :
    divergence (fun y j => dot (W y) (derivative W j y)) x =
      (∑ j, dot (derivative W j x) (derivative W j x)) + dot (W x) (laplacian W x) := by
  have hw : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hwd (j) : Differentiable ℝ (derivative W j) :=
    (derivative_contDiff hW j).differentiable (by norm_num)
  have hH : Differentiable ℝ (fun y j => dot (W y) (derivative W j y)) :=
    differentiable_pi.mpr (fun j => (dot_contDiff (hW.of_le (by norm_num))
      (derivative_contDiff hW j)).differentiable (by norm_num))
  have he (j : Fin 3) :
      derivative (fun y j => dot (W y) (derivative W j y)) j x j =
      dot (W x) (fderiv ℝ (derivative W j) x (basis j)) +
        dot (derivative W j x) (derivative W j x) := by
    change fderiv ℝ (fun y j => dot (W y) (derivative W j y)) x (basis j) j = _
    rw [← fderiv_coordinate hH]
    exact fderiv_dot hw (hwd j) x (basis j)
  simp only [divergence, he, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  exact (dot_sum_right Finset.univ (W x) (fun j =>
    fderiv ℝ (derivative W j) x (basis j))).symm

theorem integral_dot_laplacian_nonpos {L : ℝ} (hL : 0 ≤ L) {W : Space → Space}
    (hW : ContDiff ℝ 2 W) (hp : CubePeriodic L W) :
    (∫ x in fundamentalCube L, dot (W x) (laplacian W x)) ≤ 0 := by
  let H : Space → Space := fun x j => dot (W x) (derivative W j x)
  have hH : ContDiff ℝ 1 H := contDiff_pi.mpr (fun j =>
    dot_contDiff (hW.of_le (by norm_num)) (derivative_contDiff hW j))
  have hHp : CubePeriodic L H := by
    intro x n
    ext j
    dsimp [H]
    rw [hp, hp.derivative (hW.differentiable (by norm_num))]
  have hz := integral_periodic_divergence hL hH hHp
  change (∫ x in fundamentalCube L, divergence (fun y j => dot (W y) (derivative W j y)) x) = 0 at hz
  have hwd (j) := (derivative_contDiff hW j).continuous
  have hsum : Continuous (fun x => ∑ j, dot (derivative W j x) (derivative W j x)) :=
    continuous_finsetSum _ (fun j _ => dot_continuous (hwd j) (hwd j))
  have hlap : Continuous (laplacian W) := continuous_finsetSum _ (fun j _ =>
    ((derivative_contDiff hW j).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  simp only [divergence_dot_derivative hW] at hz
  have hsumi : IntegrableOn (fun x => ∑ j, dot (derivative W j x) (derivative W j x))
      (fundamentalCube L) := hsum.integrableOn_Icc
  have hlapi : IntegrableOn (fun x => dot (W x) (laplacian W x)) (fundamentalCube L) :=
    (dot_continuous hW.continuous hlap).integrableOn_Icc
  rw [integral_add hsumi hlapi] at hz
  have hn : 0 ≤ ∫ x in fundamentalCube L, ∑ j, dot (derivative W j x) (derivative W j x) :=
    integral_nonneg (fun point => Finset.sum_nonneg (fun coordinate _ =>
      dot_self_nonneg (derivative W coordinate point)))
  linarith

end ShearFlows

end

end OAI

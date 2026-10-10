import OAI.Geometry.Riemannian.HarmonicCore.Model
import OAI.Geometry.Riemannian.HarmonicCore.Energy

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution

namespace HarmonicCounterexample.Main.SmoothMetric3
open scoped InnerProductSpace

lemma christoffel_contDiff (g : SmoothMetric3) (l i j : Fin 3) :
    ContDiff ℝ ∞ (fun x ↦ g.christoffel x l i j) := by
  unfold christoffel
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro q _
  exact (g.inverse_contDiff l q).mul
    ((((g.smooth j q).fderiv_right (by simp) |>.clm_apply contDiff_const).add
      ((g.smooth i q).fderiv_right (by simp) |>.clm_apply contDiff_const)).sub
      ((g.smooth i j).fderiv_right (by simp) |>.clm_apply contDiff_const))

lemma laplacian_add_at (g : SmoothMetric3) {f h : E3 → ℝ} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) (hh : ContDiffAt ℝ 2 h x) :
    g.laplacian (f+h) x = g.laplacian f x + g.laplacian h x := by
  unfold laplacian coordDeriv
  rw [iteratedFDeriv_add_apply hf hh,
    fderiv_add (hf.differentiableAt (by norm_num)) (hh.differentiableAt (by norm_num))]
  simp only [add_apply,mul_add,
    Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_add_distrib]
  ring

lemma laplacian_smul_at (g : SmoothMetric3) {f : E3 → ℝ} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) (c : ℝ) :
    g.laplacian (c • f) x = c * g.laplacian f x := by
  unfold laplacian coordDeriv
  rw [iteratedFDeriv_const_smul_apply hf,
    fderiv_const_smul (hf.differentiableAt (by norm_num))]
  simp only [smul_apply,smul_eq_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : (∑ q, g.christoffel x q i j * (c * fderiv ℝ f x (coordinateVector q))) =
      c * ∑ q, g.christoffel x q i j * fderiv ℝ f x (coordinateVector q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hs]
  ring

lemma laplacian_const (g : SmoothMetric3) (c : ℝ) (x : E3) :
    g.laplacian (fun _ ↦ c) x = 0 := by
  simp [laplacian,coordDeriv,iteratedFDeriv_const_of_ne]

def planeExponential (L : ℝ) (p x : E3) : ℝ := Real.exp (L*⟪p,x⟫_ℝ)

lemma planeExponential_smooth (L : ℝ) (p : E3) : ContDiff ℝ ∞ (planeExponential L p) :=
  (contDiff_const.mul ((innerSL ℝ p).contDiff)).exp

lemma fderiv_planeExponential (L : ℝ) (p x : E3) :
    fderiv ℝ (planeExponential L p) x = ((planeExponential L p x)*L) • innerSL ℝ p := by
  change fderiv ℝ (fun y : E3 ↦ Real.exp (L*⟪p,y⟫_ℝ)) x = _
  simpa only [planeExponential,smul_smul,innerSL_apply_apply] using ((((innerSL ℝ p).hasFDerivAt (x:=x)).const_mul L).exp).fderiv

lemma inner_coordinateVector (p : E3) (i : Fin 3) : ⟪p,coordinateVector i⟫_ℝ=p i := by
  simp [PiLp.inner_apply,coordinateVector,RCLike.inner_apply]

lemma laplacian_planeExponential (g : SmoothMetric3) (L : ℝ) (p x : E3) :
    g.laplacian (planeExponential L p) x = planeExponential L p x*L *
      (L*(∑ i, ∑ j, (g.coeff x)⁻¹ i j*p i*p j) -
        ∑ i, ∑ j, ∑ l, (g.coeff x)⁻¹ i j*g.christoffel x l i j*p l) := by
  have hfd : fderiv ℝ (planeExponential L p) =
      fun y ↦ (planeExponential L p y*L) • innerSL ℝ p := funext (fderiv_planeExponential L p)
  have hsd : fderiv ℝ (fderiv ℝ (planeExponential L p)) x =
      (fderiv ℝ (fun y ↦ planeExponential L p y*L) x).smulRight (innerSL ℝ p) := by
    rw [hfd]
    exact fderiv_smul_const ((planeExponential_smooth L p).differentiable (by simp) x |>.mul_const L) (innerSL ℝ p)
  unfold laplacian coordDeriv
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,hsd,
    fderiv_mul_const ((planeExponential_smooth L p).differentiable (by simp) x) L,
    fderiv_planeExponential,ContinuousLinearMap.smulRight_apply,smul_eq_mul,
    smul_apply,innerSL_apply_apply,inner_coordinateVector]
  simp only [Fin.sum_univ_three]
  ring

lemma exists_positive_planeExponential (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R)
    (p : E3) (hp : p ≠ 0) : ∃ L : ℝ, 0 < L ∧
      ∀ x ∈ Metric.closedBall (0:E3) R, 0 < g.laplacian (planeExponential L p) x := by
  let Q : E3 → ℝ := fun x ↦ ∑ i, ∑ j, (g.coeff x)⁻¹ i j*p i*p j
  let B : E3 → ℝ := fun x ↦ ∑ i, ∑ j, ∑ l, (g.coeff x)⁻¹ i j*g.christoffel x l i j*p l
  have hQc : Continuous Q := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (((g.inverse_contDiff i j).continuous.mul continuous_const).mul continuous_const)
  have hBc : Continuous B := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro l _
    exact (((g.inverse_contDiff i j).continuous.mul (g.christoffel_contDiff l i j).continuous).mul continuous_const)
  have hc := isCompact_closedBall (0:E3) R
  obtain ⟨y,hy,hmin⟩ := hc.exists_isMinOn (show (Metric.closedBall (0:E3) R).Nonempty from ⟨0,by simpa using hR⟩) hQc.continuousOn
  have hpy : 0 < Q y := by
    have hp' : p.ofLp ≠ 0 := fun h ↦ hp (congrArg (WithLp.toLp 2) h)
    have h := (g.positive y).inv.dotProduct_mulVec_pos hp'
    simpa only [Q,dotProduct,star_trivial,Matrix.mulVec,Finset.mul_sum,mul_left_comm,mul_comm,mul_assoc] using h
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn hBc.continuousOn
  let L := (|C|+1)/Q y
  have hL : 0<L := div_pos (by positivity) hpy
  refine ⟨L,hL,fun x hx ↦ ?_⟩
  rw [g.laplacian_planeExponential]
  apply mul_pos (mul_pos (Real.exp_pos _) hL)
  have hQ : Q y ≤ Q x := hmin hx
  have hB : B x ≤ |C| := (le_abs_self _).trans ((hC x hx).trans (le_abs_self C))
  have hLQ : L*Q y=|C|+1 := div_mul_cancel₀ _ hpy.ne'
  change 0 < L*Q x-B x
  nlinarith

lemma supporting_plane_strict (R : ℝ) (p x : E3) (hp : ‖p‖=R)
    (hx : ‖x‖ ≤ R) (hne : x ≠ p) : ⟪p,x⟫_ℝ < R^2 := by
  have hdist : 0 < ‖x-p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hid := norm_sub_sq_real x p
  rw [real_inner_comm p x,hp] at hid
  have hR : 0 ≤ R := hp ▸ norm_nonneg p
  have hsq : ‖x‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg x) hx 2
  nlinarith

theorem exists_boundary_barrier (g : SmoothMetric3) (R : ℝ) (hR : 0<R) (p : E3) (hp : ‖p‖=R) :
    ∃ b : E3 → ℝ, ContDiff ℝ ∞ b ∧ b p=0 ∧
      (∀ x ∈ Metric.closedBall (0:E3) R, x ≠ p → 0 < b x) ∧
      (∀ x ∈ Metric.closedBall (0:E3) R, g.laplacian b x < 0) := by
  have hp0 : p ≠ 0 := by intro h; simpa [h] using hp.trans_gt hR
  obtain ⟨L,hL,hLap⟩ := g.exists_positive_planeExponential R hR.le p hp0
  let b : E3 → ℝ := fun x ↦ planeExponential L p p-planeExponential L p x
  have hbs : ContDiff ℝ ∞ b := contDiff_const.sub (planeExponential_smooth L p)
  refine ⟨b,hbs,sub_self _,?_,?_⟩
  · intro x hx hxp
    have hin := supporting_plane_strict R p x hp (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx) hxp
    apply sub_pos.mpr
    apply Real.exp_lt_exp.mpr
    rw [real_inner_self_eq_norm_sq,hp]
    exact mul_lt_mul_of_pos_left hin hL
  · intro x hx
    have hh := hLap x hx
    have hconst : g.laplacian (fun _ : E3 ↦ planeExponential L p p) x=0 := g.laplacian_const _ _
    have hde : b = (fun _ ↦ planeExponential L p p)+(-1:ℝ) • planeExponential L p := by funext; simp [b,sub_eq_add_neg]
    have hf2 : ContDiffAt ℝ 2 (planeExponential L p) x :=
      ((planeExponential_smooth L p).of_le (by norm_cast)).contDiffAt
    have hm2 : ContDiffAt ℝ 2 ((-1:ℝ) • planeExponential L p) x := hf2.const_smul (-1:ℝ)
    rw [hde,g.laplacian_add_at contDiffAt_const hm2,g.laplacian_smul_at hf2 (-1:ℝ),hconst]
    linarith

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI

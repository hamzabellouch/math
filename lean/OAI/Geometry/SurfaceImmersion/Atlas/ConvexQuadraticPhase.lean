import OAI.Geometry.SurfaceImmersion.Correction.SmoothPhaseChart
import OAI.Geometry.Immersion.ClosedSurface.PhaseMean

namespace OAI

/-! The actual convex phases used in finite primitive preparation. Their
coordinate covariant Hessians are uniformly positive on a sufficiently
small disk when the metric connection has a fixed bound. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def convexQuadraticPhase (ell : Base) (L : ℝ) (p : Base) : ℝ :=
  phaseLinear ell p + (L / 2) * (p.1^2 + p.2^2)

lemma convexQuadraticPhase_smooth (ell : Base) (L : ℝ) :
    ContDiff ℝ ∞ (convexQuadraticPhase ell L) := by
  exact (phaseLinear ell).contDiff.add
    (contDiff_const.mul ((contDiff_fst.pow 2).add (contDiff_snd.pow 2)))

lemma convexQuadraticPhase_hasFDerivAt (ell : Base) (L : ℝ) (p : Base) :
    HasFDerivAt (convexQuadraticPhase ell L) (phaseLinear (ell + L • p)) p := by
  have h1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := p)
  have h2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := p)
  have hh := (phaseLinear ell).hasFDerivAt (x := p) |>.add
    (((h1.pow 2).add (h2.pow 2)).const_mul (L / 2))
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, smul_apply, phaseLinear_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    two_smul, smul_eq_mul]
  ring

lemma convexQuadraticPhase_coordDeriv (ell : Base) (L : ℝ) (p v : Base) :
    coordDeriv v (convexQuadraticPhase ell L) p = phaseLinear (ell + L • p) v := by
  exact congrArg (fun f : Base →L[ℝ] ℝ => f v)
    (convexQuadraticPhase_hasFDerivAt ell L p).fderiv

lemma convexQuadraticPhase_phaseDerivative (ell : Base) (L : ℝ) (p : Base) :
    phaseDerivative (convexQuadraticPhase ell L) p = ell + L • p := by
  unfold phaseDerivative
  rw [(convexQuadraticPhase_hasFDerivAt ell L p).fderiv]
  ext <;> simp [phaseLinear_apply, dx, dy]

lemma convexQuadraticPhase_regular {ell p : Base} {L : ℝ} (hL : 0 ≤ L)
    (hp : L * ‖p‖ < ‖ell‖) : phaseDerivative (convexQuadraticPhase ell L) p ≠ 0 := by
  rw [convexQuadraticPhase_phaseDerivative]
  intro he
  have heq : ell = -(L • p) := eq_neg_of_add_eq_zero_left he
  rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL] at hp
  exact (lt_irrefl _ hp)

theorem convexQuadraticPhase_chart {ell p : Base} {L : ℝ} (hL : 0 ≤ L)
    (hp : L * ‖p‖ < ‖ell‖) :
    ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
      (∀ x, (e x).1 = convexQuadraticPhase ell L x) ∧
      ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target :=
  exists_smooth_phase_chart (convexQuadraticPhase_smooth ell L)
    (convexQuadraticPhase_regular hL hp)

lemma convexQuadraticPhase_second (ell : Base) (L : ℝ) (p v w : Base) :
    coordDeriv v (coordDeriv w (convexQuadraticPhase ell L)) p =
      L * (v.1*w.1 + v.2*w.2) := by
  have he : coordDeriv w (convexQuadraticPhase ell L) =
      fun p => phaseLinear ell w + L * phaseLinear w p := by
    funext q
    rw [convexQuadraticPhase_coordDeriv]
    simp only [phaseLinear_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  rw [he]
  have hh := (hasFDerivAt_const (phaseLinear ell w) p).add
    ((phaseLinear w).hasFDerivAt (x := p) |>.const_mul L)
  change (fderiv ℝ ((fun _ : Base => phaseLinear ell w) +
    fun p => L * phaseLinear w p) p) v = _
  rw [hh.fderiv]
  simp only [smul_apply, smul_eq_mul, zero_add, phaseLinear_apply]
  ring

/-- A metric value together with its first coordinate derivative. -/
abbrev MetricFirstJet := PhaseMean.Tensor × (Base →L[ℝ] PhaseMean.Tensor)

def metricJetDet (J : MetricFirstJet) : ℝ := J.1 0 * J.1 2 - (J.1 1)^2

/-- The three symmetric Christoffel slots, with values in the coordinate
tangent plane, computed from the metric and its first derivatives. -/
def metricConnectionAt (J : MetricFirstJet) : Fin 3 → Base :=
  let a : Fin 3 → ℝ := ![J.2 dx 0 / 2, J.2 dy 0 / 2, J.2 dy 1 - J.2 dx 2 / 2]
  let b : Fin 3 → ℝ := ![J.2 dx 1 - J.2 dy 0 / 2, J.2 dx 2 / 2, J.2 dy 2 / 2]
  fun i => ((J.1 2 * a i - J.1 1 * b i) / metricJetDet J,
    (J.1 0 * b i - J.1 1 * a i) / metricJetDet J)

lemma metricConnectionAt_contDiffAt {J : MetricFirstJet} (hJ : metricJetDet J ≠ 0) :
    ContDiffAt ℝ ∞ metricConnectionAt J := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;>
    simp only [metricConnectionAt, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    unfold metricJetDet at * <;> fun_prop (disch := exact hJ)

theorem compact_metricConnection_bound {K : Set MetricFirstJet} (hK : IsCompact K)
    (hdet : ∀ J ∈ K, metricJetDet J ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ J ∈ K, ∀ i, ‖metricConnectionAt J i‖ ≤ B := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (fun J hJ => (metricConnectionAt_contDiffAt (hdet J hJ)).continuousAt.continuousWithinAt)
  refine ⟨max 0 B, le_max_left _ _, fun J hJ i => ?_⟩
  exact (norm_le_pi_norm _ i).trans ((hB J hJ).trans (le_max_right _ _))

def connectionContract (Gamma : Fin 3 → Base) (v w : Base) : Base :=
  (v.1*w.1) • Gamma 0 + (v.1*w.2 + v.2*w.1) • Gamma 1 + (v.2*w.2) • Gamma 2

def coordinateMetricHessian (h : Base → PhaseMean.Tensor) (phi : Base → ℝ)
    (p v w : Base) : ℝ :=
  coordDeriv v (coordDeriv w phi) p -
    phaseLinear (phaseDerivative phi p) (connectionContract (metricConnectionAt (h p,fderiv ℝ h p)) v w)

lemma convexQuadraticPhase_hessian (h : Base → PhaseMean.Tensor) (ell : Base) (L : ℝ)
    (p v w : Base) :
    coordinateMetricHessian h (convexQuadraticPhase ell L) p v w =
      L * (v.1*w.1 + v.2*w.2) - phaseLinear (ell + L • p)
        (connectionContract (metricConnectionAt (h p,fderiv ℝ h p)) v w) := by
  rw [coordinateMetricHessian, convexQuadraticPhase_second,
    convexQuadraticPhase_phaseDerivative]

lemma coordinateMetricHessian_fst_dy (h : Base → PhaseMean.Tensor) (p : Base) :
    coordinateMetricHessian h (Prod.fst : Base → ℝ) p dy dy =
      -(metricConnectionAt (h p,fderiv ℝ h p) 2).1 := by
  have he : convexQuadraticPhase dx 0 = (Prod.fst : Base → ℝ) := by
    funext q
    simp [convexQuadraticPhase, phaseLinear_apply, dx]
  have hh := convexQuadraticPhase_hessian h dx 0 p dy dy
  rw [he] at hh
  simpa [connectionContract, phaseLinear_apply, dx, dy] using hh

private lemma abs_quadratic_combination {a b c B x y : ℝ} (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B) :
    |x^2*a + (x*y+y*x)*b + y^2*c| ≤ 2*B*(x^2+y^2) := by
  have hm : x*y+y*x = 2*x*y := by ring
  rw [hm]
  have h1 : |x^2*a| ≤ x^2*B := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
    exact mul_le_mul_of_nonneg_left ha (sq_nonneg x)
  have h2 : |2*x*y*b| ≤ 2 * |x| * |y| * B := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have h3 : |y^2*c| ≤ y^2*B := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg y)]
    exact mul_le_mul_of_nonneg_left hc (sq_nonneg y)
  have hxy : 2 * |x| * |y| ≤ x^2+y^2 := by
    nlinarith [sq_nonneg (|x|-|y|), sq_abs x, sq_abs y]
  have hmB := mul_le_mul_of_nonneg_right hxy hB
  have htri := (abs_add_le (x^2*a+2*x*y*b) (y^2*c)).trans
    (add_le_add (abs_add_le (x^2*a) (2*x*y*b)) le_rfl)
  nlinarith

lemma connectionContract_diagonal_bound {Gamma : Fin 3 → Base} {B : ℝ}
    (hB : 0 ≤ B) (hGamma : ∀ i, ‖Gamma i‖ ≤ B) (v : Base) :
    |(connectionContract Gamma v v).1| ≤ 2*B*(v.1^2+v.2^2) ∧
      |(connectionContract Gamma v v).2| ≤ 2*B*(v.1^2+v.2^2) := by
  have h1 (i : Fin 3) : |(Gamma i).1| ≤ B := by
    exact (norm_fst_le (Gamma i)).trans (hGamma i)
  have h2 (i : Fin 3) : |(Gamma i).2| ≤ B := by
    exact (norm_snd_le (Gamma i)).trans (hGamma i)
  constructor
  · simpa only [connectionContract, Prod.fst_add, Prod.smul_fst, smul_eq_mul, pow_two] using
      (abs_quadratic_combination (x := v.1) (y := v.2) hB (h1 0) (h1 1) (h1 2))
  · simpa only [connectionContract, Prod.snd_add, Prod.smul_snd, smul_eq_mul, pow_two] using
      (abs_quadratic_combination (x := v.1) (y := v.2) hB (h2 0) (h2 1) (h2 2))

theorem convexQuadraticPhase_hessian_lower {h : Base → PhaseMean.Tensor}
    {ell p : Base} {L B K r : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hK : ‖ell‖ ≤ K) (hp : ‖p‖ ≤ r)
    (hGamma : ∀ i, ‖metricConnectionAt (h p,fderiv ℝ h p) i‖ ≤ B)
    (v : Base) :
    (L - 4*B*(K+L*r)) * (v.1^2+v.2^2) ≤
      coordinateMetricHessian h (convexQuadraticPhase ell L) p v v := by
  have hg1 : |ell.1+L*p.1| ≤ K+L*r := by
    calc
      _ ≤ |ell.1|+|L*p.1| := abs_add_le _ _
      _ ≤ K+L*r := by
        rw [abs_mul, abs_of_nonneg hL]
        exact add_le_add ((norm_fst_le ell).trans hK)
          (mul_le_mul_of_nonneg_left ((norm_fst_le p).trans hp) hL)
  have hg2 : |ell.2+L*p.2| ≤ K+L*r := by
    calc
      _ ≤ |ell.2|+|L*p.2| := abs_add_le _ _
      _ ≤ K+L*r := by
        rw [abs_mul, abs_of_nonneg hL]
        exact add_le_add ((norm_snd_le ell).trans hK)
          (mul_le_mul_of_nonneg_left ((norm_snd_le p).trans hp) hL)
  obtain ⟨hc1,hc2⟩ := connectionContract_diagonal_bound hB hGamma v
  let C := connectionContract (metricConnectionAt (h p,fderiv ℝ h p)) v v
  have hdot : |phaseLinear (ell+L • p) C| ≤ 4*B*(K+L*r)*(v.1^2+v.2^2) := by
    have hk : 0 ≤ K+L*r := (abs_nonneg _).trans hg1
    calc
      _ ≤ |ell.1+L*p.1| * |C.1| + |ell.2+L*p.2| * |C.2| := by
        simpa only [phaseLinear_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul, abs_mul] using
          abs_add_le ((ell.1+L*p.1)*C.1) ((ell.2+L*p.2)*C.2)
      _ ≤ (K+L*r)*(2*B*(v.1^2+v.2^2)) +
          (K+L*r)*(2*B*(v.1^2+v.2^2)) :=
        add_le_add (mul_le_mul hg1 hc1 (abs_nonneg _) hk)
          (mul_le_mul hg2 hc2 (abs_nonneg _) hk)
      _ = _ := by ring
  rw [convexQuadraticPhase_hessian]
  have hh := (le_abs_self (phaseLinear (ell+L • p) C)).trans hdot
  dsimp only [C] at hh
  nlinarith

/-- The radius and quadratic coefficient are chosen from the connection
and linear-covector bounds, before the individual metric or point. -/
theorem exists_uniform_convex_quadratic_phases {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧
      ∀ (h : Base → PhaseMean.Tensor) (ell p : Base), ‖ell‖ ≤ K → ‖p‖ ≤ r →
        (∀ i, ‖metricConnectionAt (h p,fderiv ℝ h p) i‖ ≤ B) →
        ∀ v : Base, (L/2)*(v.1^2+v.2^2) ≤
          coordinateMetricHessian h (convexQuadraticPhase ell L) p v v := by
  let L := 16*(B+1)*(K+1)
  let r := (16*(B+1))⁻¹
  have hBp : 0 < 16*(B+1) := by positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hr : 0 < r := inv_pos.mpr hBp
  have hLr : L*r = K+1 := by
    dsimp [L,r]
    field_simp [hBp.ne']
  have hsmall : 4*B*(K+L*r) ≤ L/2 := by
    rw [hLr]
    dsimp [L]
    nlinarith
  refine ⟨L,r,hL,hr,fun h ell p hell hp hGamma v => ?_⟩
  have hb := convexQuadraticPhase_hessian_lower hL.le hB hell hp hGamma v
  nlinarith [mul_le_mul_of_nonneg_right hsmall (add_nonneg (sq_nonneg v.1) (sq_nonneg v.2))]

theorem compact_uniform_convex_quadratic_phases {J : Set MetricFirstJet}
    (hJ : IsCompact J) (hdet : ∀ j ∈ J, metricJetDet j ≠ 0)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧
      ∀ (h : Base → PhaseMean.Tensor) (ell p : Base), ‖ell‖ ≤ K → ‖p‖ ≤ r →
        (h p,fderiv ℝ h p) ∈ J → ∀ v : Base,
        (L/2)*(v.1^2+v.2^2) ≤
          coordinateMetricHessian h (convexQuadraticPhase ell L) p v v := by
  obtain ⟨B,hB,hbound⟩ := compact_metricConnection_bound hJ hdet
  obtain ⟨L,r,hL,hr,hphase⟩ := exists_uniform_convex_quadratic_phases hB hK
  exact ⟨L,r,hL,hr,fun h ell p hell hp hj v => hphase h ell p hell hp (hbound _ hj) v⟩

/-- One disk and one quadratic coefficient work for all three phase
covectors and every metric whose first jet belongs to the fixed compact
set. Each phase has positive Hessian and is a genuine local coordinate. -/
theorem finite_uniform_convex_phase_charts {J : Set MetricFirstJet}
    (hJ : IsCompact J) (hdet : ∀ j ∈ J, metricJetDet j ≠ 0)
    (ell : Fin 3 → Base) (hell : ∀ i, ell i ≠ 0) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧
      ∀ (h : Base → PhaseMean.Tensor) (p : Base), ‖p‖ ≤ r →
        (h p,fderiv ℝ h p) ∈ J → ∀ i,
          (∀ v : Base, v ≠ 0 →
            0 < coordinateMetricHessian h (convexQuadraticPhase (ell i) L) p v v) ∧
          ∃ e : OpenPartialHomeomorph Base Base, p ∈ e.source ∧
            (∀ x, (e x).1 = convexQuadraticPhase (ell i) L x) ∧
            ContDiff ℝ ∞ e ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  obtain ⟨L,r,hL,hr,hphase⟩ := compact_uniform_convex_quadratic_phases hJ hdet (norm_nonneg ell)
  let a := Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 => ‖ell i‖)
  have ha : 0 < a := (Finset.lt_inf'_iff _).mpr
    (fun i _ => norm_pos_iff.mpr (hell i))
  let r' := min r (a/(2*L))
  have hr' : 0 < r' := lt_min hr (div_pos ha (mul_pos (by norm_num) hL))
  refine ⟨L,r',hL,hr',fun h p hp hj i => ?_⟩
  have hp' : ‖p‖ ≤ r := hp.trans (min_le_left _ _)
  have ha_i : a ≤ ‖ell i‖ := Finset.inf'_le _ (Finset.mem_univ i)
  have hregular : L*‖p‖ < ‖ell i‖ := by
    have hsmall : L*‖p‖ ≤ a/2 := by
      calc
        _ ≤ L*(a/(2*L)) := mul_le_mul_of_nonneg_left (hp.trans (min_le_right _ _)) hL.le
        _ = a/2 := by field_simp [hL.ne']
    linarith
  refine ⟨?_,convexQuadraticPhase_chart hL.le hregular⟩
  intro v hv
  have hq0 : v.1^2+v.2^2 ≠ 0 := by
    intro hz
    obtain ⟨hv1,hv2⟩ := sq_add_sq_eq_zero.mp hz
    exact hv (Prod.ext hv1 hv2)
  have hq : 0 < v.1^2+v.2^2 := lt_of_le_of_ne
    (add_nonneg (sq_nonneg v.1) (sq_nonneg v.2)) (Ne.symm hq0)
  exact (mul_pos (half_pos hL) hq).trans_le
    (hphase h (ell i) p (norm_le_pi_norm ell i) hp' hj v)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI

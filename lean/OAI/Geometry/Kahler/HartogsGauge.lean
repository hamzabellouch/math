import OAI.Geometry.Kahler.HartogsCharts

namespace OAI

open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs

lemma dz_re_holomorphic {f : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℂ f p) (i : Fin 3) :
    dz (fun q => ((f q).re : ℂ)) p i = dz f p i / 2 := by
  have he : (fun q => ((f q).re : ℂ)) = fun q => (1/2 : ℂ) * (f q + star (f q)) := by
    funext q
    rw [Complex.re_eq_add_conj]
    change (f q + star (f q)) / 2 = _
    ring
  have hc : DifferentiableAt ℝ (fun q => star (f q)) p :=
    Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp p (hf.restrictScalars ℝ)
  rw [he]
  erw [dz_const_mul ((hf.restrictScalars ℝ).add hc),
    dz_add (hf.restrictScalars ℝ) hc,
    dz_conj (hf.restrictScalars ℝ), dbar_holomorphic hf, star_zero, add_zero]
  ring

lemma dbar_re_holomorphic {f : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℂ f p) (i : Fin 3) :
    dbar (fun q => ((f q).re : ℂ)) p i = star (dz f p i) / 2 := by
  erw [dbar_eq_star_dz_real (Complex.reCLM.differentiableAt.comp p (hf.restrictScalars ℝ)), dz_re_holomorphic hf]
  simp

lemma dz_analyticAt {f : Ambient → ℂ} {p : Ambient}
    (hf : AnalyticAt ℂ f p) (i : Fin 3) : AnalyticAt ℂ (fun q => dz f q i) p := by
  have he : (fun q => dz f q i) =ᶠ[𝓝 p] (fun q => fderiv ℂ f q (coordVector i)) := by
    filter_upwards [hf.eventually_analyticAt] with q hq
    exact dz_holomorphic hq.differentiableAt i
  exact (((ContinuousLinearMap.apply ℂ ℂ (coordVector i)).analyticAt _).comp hf.fderiv).congr he.symm

lemma complexHessian_re_holomorphic {f : Ambient → ℂ} {p : Ambient}
    (hf : AnalyticAt ℂ f p) (i j : Fin 3) :
    complexHessian (fun q => (f q).re) p i j = 0 := by
  have he : (fun q => dbar (fun r => ((f r).re : ℂ)) q j) =ᶠ[𝓝 p]
      (fun q => (1/2 : ℂ) * star (dz f q j)) := by
    filter_upwards [hf.eventually_analyticAt] with q hq
    rw [dbar_re_holomorphic hq.differentiableAt]
    ring
  have hc : DifferentiableAt ℝ (fun q => star (dz f q j)) p :=
    Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp p
      ((dz_analyticAt hf j).differentiableAt.restrictScalars ℝ)
  unfold complexHessian
  rw [dz_congr he, dz_const_mul hc,
    dz_conj ((dz_analyticAt hf j).differentiableAt.restrictScalars ℝ),
    dbar_holomorphic (dz_analyticAt hf j).differentiableAt, star_zero, mul_zero]

lemma complexHessian_congr {f g : Ambient → ℝ} {p : Ambient}
    (he : f =ᶠ[𝓝 p] g) : complexHessian f p = complexHessian g p := by
  ext i j
  apply dz_congr
  filter_upwards [he.eventually_nhds] with q hq
  apply dbar_congr _ j
  filter_upwards [hq] with r hr
  exact congrArg Complex.ofReal hr

lemma complexHessian_gauge {f : Ambient → ℝ} {P : Ambient → ℂ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hP : AnalyticAt ℂ P p) :
    complexHessian (fun q => f q - 2*(P q).re) p = complexHessian f p := by
  have hr : ContDiffAt ℝ 2 (fun q => (P q).re) p :=
    Complex.reCLM.contDiff.contDiffAt.comp p (hP.contDiffAt.restrict_scalars ℝ)
  have he : (fun q => f q - 2*(P q).re) = fun q => f q + (-2)*(P q).re := by
    funext q; ring
  rw [he]
  ext i j
  rw [complexHessian_add hf (contDiffAt_const.mul hr),
    complexHessian_const_mul hr, complexHessian_re_holomorphic hP]
  simp

def horizontalCoordinate (i : Fin 2) : Ambient →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => ℂ)).toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℂ Base ℂ))

@[simp] lemma horizontalCoordinate_apply (i : Fin 2) (p : Ambient) :
    horizontalCoordinate i p = p.1 i := rfl

@[simp] lemma horizontalCoordinate_coordVector (i : Fin 2) (j : Fin 3) :
    horizontalCoordinate i (coordVector j) = if j = i.castSucc then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [coordVector]

lemma dz_horizontal (p : Ambient) (i : Fin 2) (j : Fin 3) :
    dz (fun q : Ambient => q.1 i) p j = if j = i.castSucc then 1 else 0 := by
  exact (dz_linear (horizontalCoordinate i) p j).trans (horizontalCoordinate_coordVector i j)

def gaugePolynomial (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) (p : Ambient) : ℂ :=
  (∑ i, a i * p.1 i) + (1/2 : ℂ) * ∑ i, ∑ k, B i k * p.1 i * p.1 k

lemma gaugePolynomial_analytic (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) :
    AnalyticOnNhd ℂ (gaugePolynomial a B) univ := by
  intro p hp
  have h (i : Fin 2) : AnalyticAt ℂ (fun q : Ambient => q.1 i) p :=
    (horizontalCoordinate i).analyticAt p
  unfold gaugePolynomial
  simp only [Fin.sum_univ_two]
  exact ((analyticAt_const.mul (h 0)).add (analyticAt_const.mul (h 1))).add
    (analyticAt_const.mul
      ((((analyticAt_const.mul (h 0)).mul (h 0)).add ((analyticAt_const.mul (h 0)).mul (h 1))).add
       (((analyticAt_const.mul (h 1)).mul (h 0)).add ((analyticAt_const.mul (h 1)).mul (h 1)))))

@[simp] lemma gaugePolynomial_center (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) (w : ℂ) :
    gaugePolynomial a B (0,w) = 0 := by simp [gaugePolynomial]

lemma dz_gaugePolynomial (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) (p : Ambient)
    (j : Fin 3) :
    dz (gaugePolynomial a B) p j =
      (∑ i, a i * (if j = i.castSucc then 1 else 0)) +
      (1/2 : ℂ) * ∑ i, ∑ k, B i k *
        ((if j = i.castSucc then 1 else 0) * p.1 k + p.1 i * (if j = k.castSucc then 1 else 0)) := by
  unfold gaugePolynomial
  simp only [Fin.sum_univ_two]
  simp (disch := fun_prop) only [dz_add, dz_const_mul, dz_mul, dz_horizontal]
  ring

lemma dz_gaugePolynomial_center (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) (w : ℂ)
    (i : Fin 2) : dz (gaugePolynomial a B) (0,w) i.castSucc = a i := by
  rw [dz_gaugePolynomial]
  fin_cases i <;> simp [Fin.sum_univ_two]

lemma dz_dz_gaugePolynomial (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ)
    (hB : ∀ i k, B i k = B k i) (p : Ambient) (i k : Fin 2) :
    dz (fun q => dz (gaugePolynomial a B) q k.castSucc) p i.castSucc = B i k := by
  simp only [dz_gaugePolynomial, Fin.sum_univ_two]
  fin_cases i <;> fin_cases k <;>
    simp (disch := fun_prop) only [Fin.reduceFinMk, ↓reduceIte,
      one_mul, mul_one, dz_add, dz_const_mul,
      dz_horizontal]
  all_goals try simp [dz]
  all_goals try rw [hB 0 1]
  all_goals ring

lemma dz_sub {f g : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) (i : Fin 3) :
    dz (fun q => f q - g q) p i = dz f p i - dz g p i := by
  simp only [dz, fderiv_fun_sub hf hg, sub_apply]
  ring

lemma dz_gauge {f : Ambient → ℝ} {P : Ambient → ℂ} {p : Ambient}
    (hf : DifferentiableAt ℝ f p) (hP : DifferentiableAt ℂ P p) (i : Fin 3) :
    dz (fun q => (f q - 2*(P q).re : ℝ)) p i =
      dz (fun q => (f q : ℂ)) p i - dz P p i := by
  have hd : DifferentiableAt ℝ (fun q => ((P q).re : ℂ)) p :=
    Complex.ofRealCLM.differentiableAt.comp p (Complex.reCLM.differentiableAt.comp p (hP.restrictScalars ℝ))
  have hf' : DifferentiableAt ℝ (fun q => (f q : ℂ)) p := Complex.ofRealCLM.differentiableAt.comp p hf
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [dz_sub hf' (hd.const_mul 2), dz_const_mul hd, dz_re_holomorphic hP]
  ring

lemma dz_dz_gauge {f : Ambient → ℝ} {P : Ambient → ℂ} {p : Ambient}
    (hf : ContDiffAt ℝ 2 f p) (hP : AnalyticAt ℂ P p) (i k : Fin 3) :
    dz (fun q => dz (fun r => (f r - 2*(P r).re : ℝ)) q k) p i =
      dz (fun q => dz (fun r => (f r : ℂ)) q k) p i - dz (fun q => dz P q k) p i := by
  have he : (fun q => dz (fun r => (f r - 2*(P r).re : ℝ)) q k) =ᶠ[𝓝 p]
      (fun q => dz (fun r => (f r : ℂ)) q k - dz P q k) := by
    filter_upwards [hf.eventually (by norm_num), hP.eventually_analyticAt] with q hfq hPq
    exact dz_gauge (hfq.differentiableAt (by norm_num)) hPq.differentiableAt k
  rw [dz_congr he, dz_sub ((_root_.OAI.ContDiffAt.hartogs_dz (_root_.OAI.ContDiffAt.hartogs_real_cast hf) (m := 1) (by norm_num) k).differentiableAt (by norm_num))
    ((dz_analyticAt hP k).differentiableAt.restrictScalars ℝ)]

def firstGaugeJet (f : Ambient → ℝ) (p : Ambient) (i : Fin 2) : ℂ :=
  dz (fun q => (f q : ℂ)) p i.castSucc

def secondGaugeJet (f : Ambient → ℝ) (p : Ambient) (i k : Fin 2) : ℂ :=
  dz (fun q => dz (fun r => (f r : ℂ)) q k.castSucc) p i.castSucc

def gaugedWeight (f : Ambient → ℝ) (p q : Ambient) : ℝ :=
  f q - 2 * (gaugePolynomial (firstGaugeJet f p) (secondGaugeJet f p) q).re

lemma secondGaugeJet_symm {f : Ambient → ℝ} {p : Ambient} (hf : ContDiffAt ℝ 2 f p)
    (i k : Fin 2) : secondGaugeJet f p i k = secondGaugeJet f p k i :=
  dz_dz_comm (_root_.OAI.ContDiffAt.hartogs_real_cast hf) i.castSucc k.castSucc

lemma gaugedWeight_first_horizontal {f : Ambient → ℝ} {w : ℂ}
    (hf : ContDiffAt ℝ 2 f (0,w)) (i : Fin 2) :
    dz (fun q => (gaugedWeight f (0,w) q : ℂ)) (0,w) i.castSucc = 0 := by
  unfold gaugedWeight
  rw [dz_gauge (hf.differentiableAt (by norm_num))
    (gaugePolynomial_analytic _ _ _ (mem_univ _)).differentiableAt, dz_gaugePolynomial_center]
  exact sub_self _

lemma gaugedWeight_second_horizontal {f : Ambient → ℝ} {w : ℂ}
    (hf : ContDiffAt ℝ 2 f (0,w)) (i k : Fin 2) :
    dz (fun q => dz (fun r => (gaugedWeight f (0,w) r : ℂ)) q k.castSucc) (0,w) i.castSucc = 0 := by
  unfold gaugedWeight
  rw [dz_dz_gauge hf (gaugePolynomial_analytic _ _ _ (mem_univ _)),
    dz_dz_gaugePolynomial _ _ (secondGaugeJet_symm hf)]
  exact sub_self _

def fiberGaugeMap (C : Base → Base) (P : Ambient → ℂ) (q : Ambient) : Ambient :=
  (C q.1, Complex.exp (q.2 - P q))

def gaugeLogParameter (φ : Base → ℝ) (C : Base → Base) (P : Ambient → ℂ)
    (q : Ambient) : ℝ := φ (C q.1) + 2 * (q.2 - P q).re

lemma fiberGaugeMap_analyticAt {C : Base → Base} {P : Ambient → ℂ} {p : Ambient}
    (hC : AnalyticAt ℂ C p.1) (hP : AnalyticAt ℂ P p) :
    AnalyticAt ℂ (fiberGaugeMap C P) p := by
  have hc : AnalyticAt ℂ (fun q : Ambient => C q.1) p :=
    hC.comp ((ContinuousLinearMap.fst ℂ Base ℂ).analyticAt p)
  have hv : AnalyticAt ℂ (fun q : Ambient => q.2 - P q) p :=
    ((ContinuousLinearMap.snd ℂ Base ℂ).analyticAt p).sub hP
  exact hc.prod (analyticAt_cexp.comp hv)

lemma fiberGaugeMap_center (C : Base → Base) (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ)
    {w : ℂ} (hw : w ≠ 0) :
    fiberGaugeMap C (gaugePolynomial a B) (0,Complex.log w) = (C 0,w) := by
  simp [fiberGaugeMap, Complex.exp_log hw]

lemma metricPotential_fiberGauge (φ : Base → ℝ) (C : Base → Base) (P : Ambient → ℂ)
    (lam : ℝ) (q : Ambient) :
    metricPotential φ lam (fiberGaugeMap C P q) =
      lam * psi (C q.1) + logarithmicBarrier (gaugeLogParameter φ C P q) := by
  simp only [metricPotential, fiberGaugeMap, logarithmicBarrier, gaugeLogParameter,
    Complex.norm_exp, Real.exp_add]
  rw [show Real.exp (2*(q.2-P q).re) = (Real.exp (q.2-P q).re)^2 by
    rw [show (2 : ℝ)*(q.2-P q).re = (q.2-P q).re + (q.2-P q).re by ring, Real.exp_add]; ring]
  ring

lemma gaugeLogParameter_neg {φ : Base → ℝ} {C : Base → Base} {P : Ambient → ℂ}
    {q : Ambient} (hq : fiberGaugeMap C P q ∈ hartogs φ) :
    gaugeLogParameter φ C P q < 0 := by
  have he : Real.exp (gaugeLogParameter φ C P q) =
      Real.exp (φ (C q.1)) * ‖Complex.exp (q.2-P q)‖^2 := by
    simp only [gaugeLogParameter, Real.exp_add, Complex.norm_exp]
    rw [show (2 : ℝ)*(q.2-P q).re = (q.2-P q).re + (q.2-P q).re by ring, Real.exp_add]
    ring
  exact Real.exp_lt_one_iff.mp (he.trans_lt hq.2)

lemma jacobianMatrix_det_of_fderiv_injective {F : Ambient → Ambient} {p : Ambient}
    (hF : Function.Injective (fderiv ℂ F p)) : (jacobianMatrix F p).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  apply coordinateEquiv.symm.injective
  apply hF
  rw [← matrixPush_jacobian, ← matrixPush_jacobian]
  exact congrArg coordinateEquiv.symm huv

lemma fderiv_fiberGaugeMap {C : Base → Base} {P : Ambient → ℂ} {p : Ambient}
    (hC : DifferentiableAt ℂ C p.1) (hP : DifferentiableAt ℂ P p) (u : Ambient) :
    fderiv ℂ (fiberGaugeMap C P) p u =
      (fderiv ℂ C p.1 u.1, Complex.exp (p.2-P p) * (u.2 - fderiv ℂ P p u)) := by
  have hh : HasFDerivAt (fiberGaugeMap C P)
      ((fderiv ℂ C p.1).comp (ContinuousLinearMap.fst ℂ Base ℂ) |>.prod
        (Complex.exp (p.2-P p) • ((ContinuousLinearMap.snd ℂ Base ℂ) - fderiv ℂ P p))) p :=
    (hC.hasFDerivAt.comp p (ContinuousLinearMap.fst ℂ Base ℂ).hasFDerivAt).prodMk
      ((Complex.hasDerivAt_exp (p.2-P p)).comp_hasFDerivAt p
        ((ContinuousLinearMap.snd ℂ Base ℂ).hasFDerivAt.sub hP.hasFDerivAt))
  rw [hh.fderiv]
  rfl

lemma fderiv_gaugePolynomial_vertical (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ)
    (p : Ambient) (w : ℂ) : fderiv ℂ (gaugePolynomial a B) p (0,w) = 0 := by
  have hp := (gaugePolynomial_analytic a B p (mem_univ p)).differentiableAt
  have hr := (hp.hasFDerivAt.restrictScalars ℝ).fderiv
  have he := fderiv_wirtinger (gaugePolynomial a B) p (0,w)
  rw [hr] at he
  change fderiv ℂ (gaugePolynomial a B) p (0,w) = _ at he
  rw [he]
  simp only [dbar_holomorphic hp, dz_gaugePolynomial, coordinates, Fin.sum_univ_three]
  simp

lemma fderiv_fiberGaugeMap_injective {C : Base → Base} {p : Ambient}
    (hC : DifferentiableAt ℂ C p.1) (hCi : Function.Injective (fderiv ℂ C p.1))
    (a : Fin 2 → ℂ) (B : Fin 2 → Fin 2 → ℂ) :
    Function.Injective (fderiv ℂ (fiberGaugeMap C (gaugePolynomial a B)) p) := by
  have hP := (gaugePolynomial_analytic a B p (mem_univ p)).differentiableAt
  let L := fderiv ℂ (gaugePolynomial a B) p
  have hv (u : Ambient) : L u = L (u.1,0) := by
    have he : u = (u.1,0) + (0,u.2) := by ext <;> simp
    conv_lhs => rw [he, map_add, fderiv_gaugePolynomial_vertical, add_zero]
  intro u v huv
  rw [fderiv_fiberGaugeMap hC hP, fderiv_fiberGaugeMap hC hP] at huv
  have hbase : u.1 = v.1 := hCi (congrArg Prod.fst huv)
  have hfib := congrArg Prod.snd huv
  have hexp := Complex.exp_ne_zero (p.2-gaugePolynomial a B p)
  have hd : L u = L v := by rw [hv u, hv v, hbase]
  have hvertical : u.2 = v.2 := by
    have h := mul_left_cancel₀ hexp hfib
    change u.2 - L u = v.2 - L v at h
    rw [hd] at h
    linear_combination h
  exact Prod.ext hbase hvertical

lemma psi_chart_hessian_eventually {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) (w : ℂ) :
    complexHessian (fun q : Ambient => psi (centeredChart r U q.1)) =ᶠ[𝓝 (0,w)]
      complexHessian (fun q : Ambient => psi q.1) := by
  let P : Ambient → ℂ := fun q => (Real.log (1-r^2) / 2 : ℝ) - Complex.log (1+(r : ℂ)*q.1 0)
  have hP : AnalyticAt ℂ P (0,w) := by
    have hd : AnalyticAt ℂ (fun q : Ambient => 1 + (r : ℂ)*q.1 0) (0,w) :=
      analyticAt_const.add (analyticAt_const.mul ((horizontalCoordinate 0).analyticAt _))
    exact analyticAt_const.sub ((analyticAt_clog (by simp)).comp hd)
  have hb : ∀ᶠ q : Ambient in 𝓝 (0,w), q.1 ∈ ball :=
    continuous_fst.continuousAt (isOpen_ball.mem_nhds (by simp [ball]))
  have he : (fun q : Ambient => psi (centeredChart r U q.1)) =ᶠ[𝓝 (0,w)]
      (fun q => psi q.1 - 2*(P q).re) := by
    filter_upwards [hb] with q hq
    rw [psi_centeredChart hr hr1 U hq]
    simp only [P, Complex.sub_re, Complex.ofReal_re]
    ring
  filter_upwards [he.eventually_nhds, hb, hP.eventually_analyticAt] with q heq hq hPq
  rw [complexHessian_congr heq]
  apply complexHessian_gauge _ hPq
  exact ((psi_contDiffAt hq).comp q contDiffAt_fst).of_le (by exact WithTop.coe_le_coe.mpr le_top)

end PinchedHartogs

end

end OAI

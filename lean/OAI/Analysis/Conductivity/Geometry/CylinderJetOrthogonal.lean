import Mathlib
import OAI.Analysis.Conductivity.Fourier.PoissonTraceRate
import OAI.Analysis.Conductivity.Fourier.CylinderModeGreen

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

abbrev FiniteAxisJets (R : ℝ) := PiLp 2 (fun _ : Fin 4 => FiniteAxisL2 R)

def cylinderJetMode (R : ℝ) (h : TorusModes) :
    FiniteAxisJets R →ₗᵢ[ℂ] FiniteCylinderJets R where
  toFun q := WithLp.toLp 2 (fun j => cylinderMode (FiniteAxisMeasure R) h (q j))
  map_add' q r := by
    apply PiLp.ext
    intro j
    exact map_add (cylinderMode (FiniteAxisMeasure R) h) (q j) (r j)
  map_smul' c q := by
    apply PiLp.ext
    intro j
    exact map_smul (cylinderMode (FiniteAxisMeasure R) h) c (q j)
  norm_map' q := by
    have he : ‖WithLp.toLp 2 (fun j => cylinderMode (FiniteAxisMeasure R) h (q j))‖^2=‖q‖^2 := by
      simp only [PiLp.norm_sq_eq_of_L2,LinearIsometry.norm_map]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

lemma cylinderJetMode_orthogonal (R : ℝ) :
    OrthogonalFamily ℂ (fun _ : TorusModes => FiniteAxisJets R) (cylinderJetMode R) := by
  intro h k hne q r
  rw [PiLp.inner_apply]
  have hz (j : Fin 4) : inner ℂ ((cylinderJetMode R h q) j) ((cylinderJetMode R k r) j)=0 :=
    cylinderMode_orthogonal (FiniteAxisMeasure R) hne (q j) (r j)
  simp only [hz,Finset.sum_const_zero]

def smoothAxisModeJet {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) : FiniteAxisJets R :=
  WithLp.toLp 2 ![smoothFiniteAxisLp hq.continuous R,
    smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R,
    (Complex.I*(h 0:ℂ))•smoothFiniteAxisLp hq.continuous R,
    (Complex.I*(h 1:ℂ))•smoothFiniteAxisLp hq.continuous R]

lemma cylinderJetMode_smooth {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) :
    cylinderJetMode R h (smoothAxisModeJet hq R h)=smoothCylinderModeJet hq R h := by
  ext j
  fin_cases j <;> rfl

lemma smoothAxisModeJet_norm_sq {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) :
    ‖smoothAxisModeJet hq R h‖^2=
      ‖smoothFiniteAxisLp (hq.continuous_deriv (by simp)) R‖^2+
        (1+(h 0:ℝ)^2+(h 1:ℝ)^2)*‖smoothFiniteAxisLp hq.continuous R‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [smoothAxisModeJet,Fin.sum_univ_succ,Fin.sum_univ_zero,WithLp.ofLp_toLp,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons,Fin.succ_zero_eq_one,Fin.succ_one_eq_two,show (2:Fin 3).succ=(3:Fin 4) by rfl,norm_smul,norm_mul,
    Complex.norm_I,one_mul,mul_pow,add_zero]
  have hh (j : Fin 2) : ‖(h j:ℂ)‖^2=(h j:ℝ)^2 := by
    rw [show (h j:ℂ)=((h j:ℝ):ℂ) by norm_cast,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [hh,hh]
  ring

lemma smoothCylinder_polynomial_norm_sq (q : TorusModes → ℝ → ℂ)
    (hq : ∀ h,ContDiff ℝ (↑(⊤:ℕ∞)) (q h)) (R : ℝ) (F : Finset TorusModes) :
    ‖∑ h∈F,smoothCylinderModeJet (hq h) R h‖^2=
      ∑ h∈F,(‖smoothFiniteAxisLp ((hq h).continuous_deriv (by simp)) R‖^2+
        (1+(h 0:ℝ)^2+(h 1:ℝ)^2)*‖smoothFiniteAxisLp (hq h).continuous R‖^2) := by
  simp_rw [←cylinderJetMode_smooth]
  rw [(cylinderJetMode_orthogonal R).norm_sum]
  exact Finset.sum_congr rfl (fun h _ => smoothAxisModeJet_norm_sq (hq h) R h)

lemma smoothFiniteAxisLp_norm_sq {q : ℝ → ℂ} (hq : Continuous q) {R : ℝ} (hR : 0≤R) :
    ‖smoothFiniteAxisLp hq R‖^2=∫ t in (0:ℝ)..R,‖q t‖^2 := by
  rw [complexLp_norm_sq,intervalIntegral.integral_of_le hR]
  apply integral_congr_ae
  filter_upwards [smoothFiniteAxisLp_ae hq R] with t ht
  rw [ht]

lemma complex_fourier_mode_trace_energy_right {q : ℝ → ℂ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) {R m : ℝ} (hR : 0<R) (hm : 0 ≤ m) :
    m*‖q R‖^2≤(1+1/R)*(∫ t in (0:ℝ)..R,
      ‖deriv q t‖^2+(1+m^2)*‖q t‖^2) := by
  have hf : ContDiff ℝ (↑(⊤:ℕ∞)) (fun t => q (R-t)) :=
    hq.comp (contDiff_const.sub contDiff_id)
  have hd (t : ℝ) : deriv (fun u => q (R-u)) t= -(deriv q (R-t)) := by
    have hi : HasDerivAt (fun u : ℝ => R-u) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub R
    simpa only [Function.comp_def,neg_smul,one_smul] using
      (((hq.differentiable (by simp) (R-t)).hasDerivAt).scomp t hi).deriv
  have hb := complex_fourier_mode_trace_energy hf hR hm
  simp only [sub_zero,hd,norm_neg] at hb
  have hi := intervalIntegral.integral_comp_sub_left
    (fun t => ‖deriv q t‖^2+(1+m^2)*‖q t‖^2) (a:=0) (b:=R) R
  rw [sub_self,sub_zero] at hi
  rw [hi] at hb
  exact hb

def cylinderTraceConstant (s : Fin 3 → ℝ) (R : ℝ) : ℝ :=
  (1+1/R)*(3+2*(|s 0|+|s 1|+|s 2|))

lemma cylinderTraceConstant_pos (s : Fin 3 → ℝ) {R : ℝ} (hR : 0<R) :
    0<cylinderTraceConstant s R := by unfold cylinderTraceConstant; positivity

lemma smoothAxisMode_trace_energy_bound (s : Fin 3 → ℝ)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) {R : ℝ} (hR : 0<R) (h : TorusModes) :
    (∫ t in (0:ℝ)..R,‖deriv q t‖^2+(1+(1+torusRate s h)^2)*‖q t‖^2)≤
      (3+2*(|s 0|+|s 1|+|s 2|))*‖smoothAxisModeJet hq R h‖^2 := by
  have hd := hq.continuous_deriv (by simp)
  have hD : IntervalIntegrable (fun t => ‖deriv q t‖^2) volume 0 R :=
    (hd.norm.pow 2).intervalIntegrable _ _
  have hU : IntervalIntegrable (fun t => (1+(1+torusRate s h)^2)*‖q t‖^2) volume 0 R :=
    (continuous_const.mul (hq.continuous.norm.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hD hU,
    intervalIntegral.integral_const_mul,←smoothFiniteAxisLp_norm_sq hd hR.le,
    ←smoothFiniteAxisLp_norm_sq hq.continuous hR.le,smoothAxisModeJet_norm_sq]
  let C := |s 0|+|s 1|+|s 2|
  let n := (h 0:ℝ)^2+(h 1:ℝ)^2
  have hC : 0≤C := by dsimp [C]; positivity
  have hn : 0≤n := by dsimp [n]; positivity
  have hm := torusRate_sq_polynomial_bound s h
  change (torusRate s h)^2≤C*n at hm
  have hb : 1+(1+torusRate s h)^2≤3+2*C*n := by
    nlinarith [sq_nonneg (torusRate s h-1)]
  have hb' : 1+(1+torusRate s h)^2≤(3+2*C)*(1+(h 0:ℝ)^2+(h 1:ℝ)^2) := by
    have hcn : 0≤3*n := mul_nonneg (by norm_num) hn
    dsimp [n] at *
    nlinarith
  have hz := mul_le_mul_of_nonneg_right hb' (sq_nonneg ‖smoothFiniteAxisLp hq.continuous R‖)
  have hy := mul_le_mul_of_nonneg_right (show (1:ℝ)≤3+2*C by linarith)
    (sq_nonneg ‖smoothFiniteAxisLp hd R‖)
  dsimp only [C] at hz hy
  nlinarith only [hz,hy]

lemma smoothAxisMode_trace_left (s : Fin 3 → ℝ)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) {R : ℝ} (hR : 0<R) (h : TorusModes) :
    (1+torusRate s h)*‖q 0‖^2≤cylinderTraceConstant s R*‖smoothAxisModeJet hq R h‖^2 := by
  have hb := complex_fourier_mode_trace_energy hq hR
    (show 0≤1+torusRate s h by have := Real.sqrt_nonneg (torusQuadratic s h); dsimp [torusRate]; positivity)
  apply hb.trans
  simpa only [cylinderTraceConstant,mul_assoc] using mul_le_mul_of_nonneg_left
    (smoothAxisMode_trace_energy_bound s hq hR h) (show 0≤1+1/R by positivity)

lemma smoothAxisMode_trace_right (s : Fin 3 → ℝ)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) {R : ℝ} (hR : 0<R) (h : TorusModes) :
    (1+torusRate s h)*‖q R‖^2≤cylinderTraceConstant s R*‖smoothAxisModeJet hq R h‖^2 := by
  have hb := complex_fourier_mode_trace_energy_right hq hR
    (show 0≤1+torusRate s h by have := Real.sqrt_nonneg (torusQuadratic s h); dsimp [torusRate]; positivity)
  apply hb.trans
  simpa only [cylinderTraceConstant,mul_assoc] using mul_le_mul_of_nonneg_left
    (smoothAxisMode_trace_energy_bound s hq hR h) (show 0≤1+1/R by positivity)

end ScalarConductivity

end

end OAI

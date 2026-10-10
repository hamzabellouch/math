import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PowerSumLe
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TermMangoldtEq
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MangoldtAbscissa
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.HorizontalProductBound

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory
open Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set

namespace OrdinaryHorizontalHalasz
open MeasureTheory Set OrdinaryLogDerivative OrdinaryDirichletMeanSquare
open OrdinaryCompactCauchy OrdinaryPowerBounds

def line (δ t : ℝ) : ℂ := ((1+δ:ℝ):ℂ)-(t:ℂ)*Complex.I
@[simp] lemma line_re (δ t : ℝ) : (line δ t).re=1+δ := by simp [line]
lemma line_add (δ x t : ℝ) : line (δ+x) t = line δ t+(x:ℂ) := by
  simp only [line,Complex.ofReal_add]
  ring

def energyConstant : ℝ := gaussianConstant * Real.exp 3 * 4 *
    (chebyshevConstant * Real.exp 1)^2

def rootGaussian (t : ℝ) : ℂ := (Real.sqrt (gaussian t):ℝ)

lemma norm_rootGaussian (t : ℝ) : ‖rootGaussian t‖=Real.sqrt (gaussian t) := by
  simp [rootGaussian,Real.sqrt_nonneg]

lemma rootGaussian_sq (t : ℝ) : ‖rootGaussian t‖^2=gaussian t := by
  rw [norm_rootGaussian,Real.sq_sqrt (gaussian_nonneg t)]

lemma continuous_rootGaussian : Continuous rootGaussian := by
  unfold rootGaussian gaussian
  fun_prop

lemma continuous_lseries_comp {X : Type*} [TopologicalSpace X]
    {g : ℕ → ℂ} (hab : LSeries.abscissaOfAbsConv g ≤ (1:ℝ))
    {«φ» : X → ℂ} {U : Set X} (hφ : ContinuousOn «φ» U)
    (hφ1 : ∀x∈U, 1<(«φ» x).re) : ContinuousOn (fun x => LSeries g («φ» x)) U := by
  apply (LSeries_differentiableOn g).continuousOn.comp hφ
  intro x hx
  exact lt_of_le_of_lt hab (by exact_mod_cast hφ1 x hx)

lemma continuous_vertical {g : ℕ → ℂ} (hab : LSeries.abscissaOfAbsConv g ≤ (1:ℝ))
    {δ : ℝ} (hδ : 0<δ) : Continuous (fun t => LSeries g (line δ t)) := by
  rw [←continuousOn_univ]
  apply continuous_lseries_comp hab (by unfold line; fun_prop)
  intro x hx
  simp only [line_re]
  linarith

lemma continuous_shifted {g : ℕ → ℂ} (hab : LSeries.abscissaOfAbsConv g ≤ (1:ℝ))
    {δ : ℝ} (hδ : 0<δ) {l r : ℝ} :
    ContinuousOn (fun p : ℝ×ℝ => LSeries g (line (δ+p.1) p.2))
      (Icc 0 1 ×ˢ Icc l r) := by
  apply continuous_lseries_comp hab (by unfold line; fun_prop)
  intro p hp
  simp only [line_re]
  linarith [hp.1.1]

lemma weighted_energy_integrable {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {δ : ℝ} (hδ : 0<δ) :
    Integrable (fun t : ℝ => gaussian t*‖LSeries (mangoldtTwist f) (line δ t)‖^2) := by
  simpa only [line,mangoldt_LSeries_eq] using gaussian_series_integrable
    (mangoldt_coefficient_summable f hf hδ) (fun n => Real.log n)

lemma weighted_energy_on {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    {δ : ℝ} (hδ : 0<δ) (l r : ℝ) :
    (∫t in Icc l r, ‖rootGaussian t*LSeries (mangoldtTwist f) (line δ t)‖^2) ≤
      energyConstant*(2+1/δ) := by
  simp only [norm_mul,mul_pow,rootGaussian_sq]
  apply (integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall (fun t => mul_nonneg (gaussian_nonneg _) (sq_nonneg _)))
    (weighted_energy_integrable hf hδ)).trans
  exact mangoldt_LSeries_gaussian_energy f hf hδ

lemma root_energy_on (l r : ℝ) :
    (∫t in Icc l r, ‖rootGaussian t‖^2) ≤ ∫t : ℝ, gaussian t := by
  simp only [rootGaussian_sq]
  exact integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall gaussian_nonneg) gaussian_integrable

lemma horizontal_weighted_decomposition {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖≤1)
    (hm : Complete f) {δ : ℝ} (hδ : 0<δ) {l r : ℝ} {M : ℝ → ℝ}
    (hM : ContinuousOn M (Icc 0 1))
    (hbound : ∀x∈Icc 0 1, ∀t∈Icc l r, ‖LSeries f (line (δ+x) t)‖≤M x)
    (t : ℝ) (ht : t∈Icc l r) :
      ‖rootGaussian t*LSeries f (line δ t)‖ ≤ 2*‖rootGaussian t‖ +
        ∫x in Icc 0 1, M x*‖rootGaussian t*LSeries (mangoldtTwist f) (line (δ+x) t)‖ := by
  have hfabs := LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => hf n⟩
  have hgabs := mangoldt_abscissa hf
  have hs : 1<(line δ t).re := by simp; linarith
  have hi := horizontal_identity hf hm (line δ t) hs (a:=1) (by norm_num)
  have hhh := norm_add_le (LSeries f (line δ t+1))
    (∫x : ℝ in 0..1, LSeries (mangoldtTwist f) (line δ t+x)*LSeries f (line δ t+x))
  simp only [Complex.ofReal_one] at hi
  rw [←hi] at hhh
  have hb : ‖LSeries f (line δ t+1)‖≤2 := by
    have hh := LSeries_norm_le hf (s:=line δ t+1) (by simp; linarith)
    simp only [Complex.add_re,line_re,Complex.one_re] at hh
    have hinv : 1/(1+δ)≤1 := (div_le_one (by linarith : 0<1+δ)).mpr (by linarith)
    have he : 1+δ+1-1=1+δ := by ring
    rw [he] at hh
    linarith
  have hn := intervalIntegral.norm_integral_le_integral_norm («μ» := volume) (f:=fun x : ℝ =>
    LSeries (mangoldtTwist f) (line δ t+x)*LSeries f (line δ t+x)) (by norm_num : (0:ℝ)≤1)
  simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),←integral_Icc_eq_integral_Ioc] at hn hhh
  have hc := (continuousOn_horizontal hgabs (line δ t) hs).mul
    (continuousOn_horizontal hfabs (line δ t) hs)
  have hci := (hc.norm.mono (show Icc (0:ℝ) 1 ⊆ Ici 0 from fun x hx => hx.1)).integrableOn_Icc («μ» := volume)
  have hMi : IntegrableOn (fun x => M x*‖LSeries (mangoldtTwist f) (line (δ+x) t)‖) (Icc 0 1) := by
    have hc' := (continuousOn_horizontal hgabs (line δ t) hs).mono
      (show Icc (0:ℝ) 1 ⊆ Ici 0 from fun x hx => hx.1)
    apply ContinuousOn.integrableOn_Icc
    apply hM.mul
    simpa only [line_add] using hc'.norm
  have hmono : (∫x : ℝ in Icc 0 1, ‖LSeries (mangoldtTwist f) (line δ t+x)*LSeries f (line δ t+x)‖) ≤
      ∫x in Icc 0 1, M x*‖LSeries (mangoldtTwist f) (line (δ+x) t)‖ := by
    apply integral_mono_ae hci hMi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [Pi.mul_apply]
    rw [norm_mul,←line_add]
    exact (mul_le_mul_of_nonneg_left (hbound x hx t ht) (norm_nonneg _)).trans_eq (mul_comm _ _)
  rw [norm_mul]
  calc
    _ ≤ ‖rootGaussian t‖*(2+∫x in Icc 0 1, M x*‖LSeries (mangoldtTwist f) (line (δ+x) t)‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = _ := by
      rw [mul_add,←integral_const_mul]
      congr 1
      · ring
      · apply integral_congr_ae
        filter_upwards [] with x
        rw [norm_mul]
        ring

lemma weighted_derivative_integrand {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖≤1)
    (hm : Complete f) {δ : ℝ} (hδ : 0<δ) (t : ℝ) :
    gaussian t*‖deriv (LSeries f) (line δ t)‖ =
      ‖rootGaussian t*LSeries f (line δ t)‖*
        ‖rootGaussian t*LSeries (mangoldtTwist f) (line δ t)‖ := by
  rw [LSeries_derivative_product hf hm (by simp; linarith),norm_neg,norm_mul,norm_mul,norm_mul]
  calc
    _ = ‖rootGaussian t‖^2*(‖LSeries (mangoldtTwist f) (line δ t)‖*‖LSeries f (line δ t)‖) := by rw [rootGaussian_sq]
    _ = _ := by ring

theorem weighted_derivative_bound {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖≤1)
    (hm : Complete f) {δ : ℝ} (hδ : 0<δ) (l r : ℝ) {M : ℝ → ℝ}
    (hM : ContinuousOn M (Icc 0 1)) (hM0 : ∀x∈Icc 0 1, 0≤M x)
    (hbound : ∀x∈Icc 0 1, ∀t∈Icc l r, ‖LSeries f (line (δ+x) t)‖≤M x) :
    (∫t in Icc l r, gaussian t*‖deriv (LSeries f) (line δ t)‖) ≤
      2*Real.sqrt (∫t : ℝ, gaussian t)*Real.sqrt (energyConstant*(2+1/δ)) +
      Real.sqrt (energyConstant*(2+1/δ)) *
        (∫x in Icc 0 1, M x*Real.sqrt (energyConstant*(2+1/(δ+x)))) := by
  have hfabs := LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => hf n⟩
  have hgabs := mangoldt_abscissa hf
  have hFcont := continuous_vertical hfabs hδ
  have hGcont := continuous_vertical hgabs hδ
  have hGc : ContinuousOn (fun p : ℝ×ℝ => rootGaussian p.2*
      LSeries (mangoldtTwist f) (line (δ+p.1) p.2)) (Icc 0 1 ×ˢ Icc l r) :=
    (continuous_rootGaussian.comp continuous_snd).continuousOn.mul (continuous_shifted hgabs hδ)
  have hE : ContinuousOn (fun x : ℝ => energyConstant*(2+1/(δ+x))) (Icc 0 1) := by
    apply continuousOn_const.mul
    apply continuousOn_const.add
    apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
    intro x hx
    change δ+x ≠ 0
    linarith [hx.1]
  have hdecomp := horizontal_weighted_decomposition hf hm hδ hM hbound
  simp_rw [weighted_derivative_integrand hf hm hδ]
  have henergy : ∀x∈Icc (0:ℝ) 1, (∫t : ℝ in Icc l r,
      ‖rootGaussian t*LSeries (mangoldtTwist f) (line (δ+x) t)‖^2) ≤ energyConstant*(2+1/(δ+x)) := by
    intro x hx
    exact weighted_energy_on hf (δ:=δ+x) (by linarith [hx.1]) l r
  exact horizontal_product_bound (a:=0) (b:=1) (l:=l) (r:=r)
    (P:=rootGaussian)
    (F₀:=fun t => rootGaussian t*LSeries f (line δ t))
    (G₀:=fun t => rootGaussian t*LSeries (mangoldtTwist f) (line δ t))
    (G:=fun p => rootGaussian p.2*LSeries (mangoldtTwist f) (line (δ+p.1) p.2))
    (M:=M) (E:=fun x => energyConstant*(2+1/(δ+x))) (B:=2)
    (EP:=∫t : ℝ, gaussian t) (E₀:=energyConstant*(2+1/δ))
    continuous_rootGaussian.continuousOn
    (continuous_rootGaussian.mul hFcont).continuousOn
    (continuous_rootGaussian.mul hGcont).continuousOn hGc hM hE hM0 (by norm_num)
    (root_energy_on l r) (weighted_energy_on hf hδ l r)
    henergy hdecomp

end OrdinaryHorizontalHalasz

end

end OAI

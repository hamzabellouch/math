import OAI.Geometry.Kahler.BaseChartScale

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def anisotropicMap (k : ℕ) (r : ℝ) (z : Base) : Base :=
  WithLp.toLp 2 ![(r:ℂ)+z 0/(k:ℂ),z 1/(Real.sqrt (k:ℝ):ℂ)]

lemma anisotropicMap_analytic (k : ℕ) (r : ℝ) : AnalyticOnNhd ℂ (anisotropicMap k r) univ := by
  intro z _
  apply (baseCoordinateEquiv.symm.analyticAt _).comp
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact analyticAt_const.add ((baseCoordinate 0).analyticAt z).div_const
  · exact ((baseCoordinate 1).analyticAt z).div_const

lemma anisotropicMap_norm {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    {z : Base} (hz : ‖z‖ ≤ 1) : ‖anisotropicMap k r z‖ ≤ 1+2/(k:ℝ) := by
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk1 : 1 ≤ (k:ℝ) := by exact_mod_cast hk
  have hs : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.mpr hkpos
  have hsq := Real.sq_sqrt hkpos.le
  have h0 : ‖z 0‖ ≤ 1 := (PiLp.norm_apply_le (p := (2:ENNReal)) z 0).trans hz
  have h1 : ‖z 1‖ ≤ 1 := (PiLp.norm_apply_le (p := (2:ENNReal)) z 1).trans hz
  have hn0 : ‖(r:ℂ)+z 0/(k:ℂ)‖ ≤ 1+1/(k:ℝ) := by
    apply (norm_add_le _ _).trans
    simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr,Complex.norm_natCast]
    exact add_le_add hr1 (div_le_div_of_nonneg_right h0 hkpos.le)
  have hn1 : ‖z 1/(Real.sqrt (k:ℝ):ℂ)‖ ≤ 1/Real.sqrt (k:ℝ) := by
    simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
    exact div_le_div_of_nonneg_right h1 hs.le
  have he : ‖anisotropicMap k r z‖^2 = ‖(r:ℂ)+z 0/(k:ℂ)‖^2+‖z 1/(Real.sqrt (k:ℝ):ℂ)‖^2 := by
    simp [anisotropicMap,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hi : (1/Real.sqrt (k:ℝ))^2=1/(k:ℝ) := by rw [div_pow,hsq,one_pow]
  have hb : ‖anisotropicMap k r z‖^2 ≤ (1+1/(k:ℝ))^2+1/(k:ℝ) := by
    have ha0 := norm_nonneg ((r:ℂ)+z 0/(k:ℂ))
    have ha1 := norm_nonneg (z 1/(Real.sqrt (k:ℝ):ℂ))
    nlinarith [sq_le_sq₀ ha0 (by positivity : 0 ≤ 1+1/(k:ℝ)) |>.mpr hn0,
      sq_le_sq₀ ha1 (by positivity : 0 ≤ 1/Real.sqrt (k:ℝ)) |>.mpr hn1]
  have hipos : 0 ≤ 1/(k:ℝ) := by positivity
  rw [show (2:ℝ)/(k:ℝ)=2*(1/(k:ℝ)) by ring]
  nlinarith [sq_nonneg (1/(k:ℝ)),norm_nonneg (anisotropicMap k r z)]

lemma peak_anisotropic_bound {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k)
    {P : Finset Sphere} (hP : ProjectivelySeparated (D/Real.sqrt k) P)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (U : Base ≃ₗᵢ[ℂ] Base)
    {z : Base} (hz : ‖z‖ ≤ 1) :
    ‖peakPolynomial P k (U (anisotropicMap k r z))‖ ≤ gaussianConstant*Real.exp 2 := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have he : 1+2/(k:ℝ) ≤ Real.exp (2/(k:ℝ)) := by simpa only [add_comm] using Real.add_one_le_exp (2/(k:ℝ))
  have hp := pow_le_pow_left₀ (norm_nonneg (anisotropicMap k r z))
    ((anisotropicMap_norm hk hr hr1 hz).trans he) k
  rw [← Real.exp_nat_mul] at hp
  have hex : (k:ℝ)*(2/(k:ℝ))=2 := mul_div_cancel₀ 2 hk0
  rw [hex] at hp
  simpa only [LinearIsometryEquiv.norm_map] using
    (peak_global_bound hD hk hP (U (anisotropicMap k r z))).trans
      (mul_le_mul_of_nonneg_left (by simpa only [LinearIsometryEquiv.norm_map] using hp) gaussianConstant_pos.le)

lemma peak_anisotropic_lipschitz : ∃ B : ℝ, 0 ≤ B ∧ ∀ {D : ℝ}, 1 ≤ D → ∀ {k : ℕ}, 1 ≤ k →
    ∀ {P : Finset Sphere}, ProjectivelySeparated (D/Real.sqrt k) P → ∀ {r : ℝ}, 0 ≤ r → r ≤ 1 →
    ∀ U : Base ≃ₗᵢ[ℂ] Base, ∀ z : Base, ‖z‖ ≤ 1/2 →
    ‖peakPolynomial P k (U (anisotropicMap k r z))-peakPolynomial P k (U (anisotropicMap k r 0))‖ ≤ B*‖z‖ := by
  let B := cauchyJetConstant 1*(gaussianConstant*Real.exp 2)/(1-3/4)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (cauchyJetConstant_pos 1).le
    (mul_nonneg gaussianConstant_pos.le (Real.exp_pos _).le)) (by norm_num)
  refine ⟨B,hB,?_⟩
  intro D hD k hk P hP r hr hr1 U z hz
  let f := fun z => peakPolynomial P k (U (anisotropicMap k r z))
  have hf : AnalyticOnNhd ℂ f univ := by
    intro z _
    exact (peakPolynomial_analytic P k _ (mem_univ _)).comp
      ((U.toContinuousLinearEquiv.analyticAt _).comp (anisotropicMap_analytic k r z (mem_univ _)))
  have hb (x : Base) (hx : ‖x‖ ≤ 1/2) : ‖fderiv ℂ f x‖ ≤ B := by
    have hh := analytic_jet_bound (E := Base) (F := ℂ) (c := 0) (R := 1) (r := 3/4)
      (by norm_num) (by norm_num) (mul_nonneg gaussianConstant_pos.le (Real.exp_pos _).le)
      (hf.mono (subset_univ _)) (fun y hy => peak_anisotropic_bound hD hk hP hr hr1 U (by exact (show ‖y‖ < 1 by simpa using hy).le)) 1 x
      (by simpa using (by linarith : ‖x‖ < (3/4:ℝ)))
    simpa only [norm_iteratedFDeriv_one,pow_one,B] using hh
  have hh := (convex_closedBall (0:Base) (1/2:ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hf x (mem_univ _)).differentiableAt) (fun x hx => hb x (by simpa using hx))
    (show (0:Base) ∈ Metric.closedBall 0 (1/2:ℝ) by simp)
    (show z ∈ Metric.closedBall 0 (1/2:ℝ) by simpa using hz)
  simpa only [sub_zero] using hh

end PinchedHartogs.BaseConstruction

end

end OAI

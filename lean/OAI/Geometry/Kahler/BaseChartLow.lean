import OAI.Geometry.Kahler.BaseAnisotropic

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

def anisotropicChart (k : ℕ) (r : ℝ) (z : Base) : Base :=
  WithLp.toLp 2 ![(k:ℂ)*(((r:ℂ)+z 0)/(1+(r:ℂ)*z 0)-(r:ℂ)),
    (Real.sqrt (k:ℝ):ℂ)*(Real.sqrt (1-r^2):ℂ)*z 1/(1+(r:ℂ)*z 0)]

lemma anisotropicChart_identity {k : ℕ} (hk : 1 ≤ k) (r : ℝ)
    (U : Base ≃ₗᵢ[ℂ] Base) (z : Base) :
    U (anisotropicMap k r (anisotropicChart k r z))=centeredChart r U z := by
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hs0 : (Real.sqrt (k:ℝ):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < k by omega))).ne'
  congr 1
  ext i
  fin_cases i <;> dsimp [anisotropicMap,anisotropicChart,centeredChart]
  all_goals
    by_cases hd : 1+(r:ℂ)*z 0=0
    · simp [hd]
      <;> field_simp [hk0,hs0]
      <;> ring
    · field_simp [hk0,hs0,hd]
      <;> ring

lemma anisotropicChart_norm {k : ℕ} (hk : 1 ≤ k) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hkr : (k:ℝ)*(1-r) ≤ 1) {z : Base} (hz : ‖z‖ < (1/32:ℝ)) :
    ‖anisotropicChart k r z‖ ≤ Real.sqrt ((k:ℝ)*(1-r))/4 := by
  have hkpos : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hδ : 0 < 1-r := by linarith
  have hs : 0 < Real.sqrt ((k:ℝ)*(1-r)) := Real.sqrt_pos.mpr (mul_pos hkpos hδ)
  have hs2 := Real.sq_sqrt (mul_nonneg hkpos.le hδ.le)
  have hs1 : Real.sqrt ((k:ℝ)*(1-r)) ≤ 1 := (Real.sqrt_le_one).2 hkr
  have hkst : (k:ℝ)*(1-r) ≤ Real.sqrt ((k:ℝ)*(1-r)) := by nlinarith
  have hden := chart_small_ball hr hr1 hz
  have hdenpos : 0 < ‖1+(r:ℂ)*z 0‖ := by linarith
  have hd : 1+(r:ℂ)*z 0 ≠ 0 := norm_ne_zero_iff.mp hdenpos.ne'
  have hz0 := PiLp.norm_apply_le (p := (2:ENNReal)) z 0
  have hz1 := PiLp.norm_apply_le (p := (2:ENNReal)) z 1
  have hrr : 0 ≤ 1-r^2 := by nlinarith
  have hid : ((r:ℂ)+z 0)/(1+(r:ℂ)*z 0)-(r:ℂ) = ((1-r^2:ℝ):ℂ)*z 0/(1+(r:ℂ)*z 0) := by
    push_cast
    field_simp
    ring
  have hfirst : ‖(k:ℂ)*(((r:ℂ)+z 0)/(1+(r:ℂ)*z 0)-(r:ℂ))‖ ≤ Real.sqrt ((k:ℝ)*(1-r))/8 := by
    rw [hid,norm_mul,norm_div,norm_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrr]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hdenpos).2
    have hn : (k:ℝ)*(1-r^2) ≤ 2*((k:ℝ)*(1-r)) := by nlinarith
    have hmul : (k:ℝ)*(1-r^2)*‖z 0‖ ≤ 2*Real.sqrt ((k:ℝ)*(1-r))*(1/32) := by
      calc _ ≤ (2*((k:ℝ)*(1-r)))*‖z 0‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
           _ ≤ (2*Real.sqrt ((k:ℝ)*(1-r)))*(1/32) :=
             mul_le_mul (by nlinarith) (by linarith) (norm_nonneg _) (by positivity)
    nlinarith
  have hsprod : Real.sqrt (k:ℝ)*Real.sqrt (1-r^2) ≤ 2*Real.sqrt ((k:ℝ)*(1-r)) := by
    have h1 := Real.sq_sqrt hkpos.le
    have h2 := Real.sq_sqrt hrr
    have he : (Real.sqrt (k:ℝ)*Real.sqrt (1-r^2))^2=(k:ℝ)*(1-r^2) := by rw [mul_pow,h1,h2]
    have hn : (k:ℝ)*(1-r^2) ≤ 4*((k:ℝ)*(1-r)) := by nlinarith
    nlinarith [mul_nonneg (Real.sqrt_nonneg (k:ℝ)) (Real.sqrt_nonneg (1-r^2))]
  have hsecond : ‖(Real.sqrt (k:ℝ):ℂ)*(Real.sqrt (1-r^2):ℂ)*z 1/(1+(r:ℂ)*z 0)‖ ≤ Real.sqrt ((k:ℝ)*(1-r))/8 := by
    rw [norm_div,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_iff₀ hdenpos).2
    have hm : Real.sqrt (k:ℝ)*Real.sqrt (1-r^2)*‖z 1‖ ≤ 2*Real.sqrt ((k:ℝ)*(1-r))*(1/32) :=
      mul_le_mul hsprod (by linarith) (norm_nonneg _) (by positivity)
    nlinarith
  have hnorm : ‖anisotropicChart k r z‖^2 =
      ‖(k:ℂ)*(((r:ℂ)+z 0)/(1+(r:ℂ)*z 0)-(r:ℂ))‖^2+
      ‖(Real.sqrt (k:ℝ):ℂ)*(Real.sqrt (1-r^2):ℂ)*z 1/(1+(r:ℂ)*z 0)‖^2 := by
    simp [anisotropicChart,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  have hn0 := norm_nonneg ((k:ℂ)*(((r:ℂ)+z 0)/(1+(r:ℂ)*z 0)-(r:ℂ)))
  have hn1 := norm_nonneg ((Real.sqrt (k:ℝ):ℂ)*(Real.sqrt (1-r^2):ℂ)*z 1/(1+(r:ℂ)*z 0))
  nlinarith [norm_nonneg (anisotropicChart k r z)]

lemma peak_chart_low : ∃ B : ℝ, 0 ≤ B ∧ ∀ {D : ℝ}, 1 ≤ D → ∀ {k : ℕ}, 1 ≤ k →
    ∀ {P : Finset Sphere}, ProjectivelySeparated (D/Real.sqrt k) P → ∀ {r : ℝ}, 0 ≤ r → r < 1 →
    (k:ℝ)*(1-r) ≤ 1 → ∀ U : Base ≃ₗᵢ[ℂ] Base, ∀ z : Base, ‖z‖ < 1/32 →
    ‖peakPolynomial P k (centeredChart r U z)-peakPolynomial P k (centeredChart r U 0)‖ ≤ B*Real.sqrt ((k:ℝ)*(1-r)) := by
  obtain ⟨B,hB,hBb⟩ := peak_anisotropic_lipschitz
  refine ⟨B,hB,?_⟩
  intro D hD k hk P hP r hr hr1 hkr U z hz
  have hn := anisotropicChart_norm hk hr hr1 hkr hz
  have hs1 : Real.sqrt ((k:ℝ)*(1-r)) ≤ 1 := Real.sqrt_le_one.mpr hkr
  have hn1 : ‖anisotropicChart k r z‖ ≤ 1/2 := by linarith
  have hh := hBb hD hk hP hr hr1.le U _ hn1
  rw [anisotropicChart_identity hk] at hh
  have hzero : U (anisotropicMap k r 0)=centeredChart r U 0 := by
    unfold anisotropicMap centeredChart
    simp
  rw [hzero] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hn hB).trans (by nlinarith [Real.sqrt_nonneg ((k:ℝ)*(1-r))]))

end PinchedHartogs.BaseConstruction

end

end OAI

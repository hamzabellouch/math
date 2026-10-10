import Mathlib
import OAI.Geometry.SmoothYau.Estimates.PolynomialGaussianTailTendsto

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace YauCounterexamples

def packetAxisShift (x : NormalWaveSpace) (n ε ℓ : ℝ) (j : Fin 3) : NormalWaveSpace :=
  x+(ε/(n*ℓ)) • EuclideanSpace.basisFun (Fin 3) ℝ j

lemma packetAxisShift_step {n ε ℓ : ℝ} (hn : 0 < n) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hℓ : 1 ≤ ℓ) (x : NormalWaveSpace) (j : Fin 3) :
    n*‖packetAxisShift x n ε ℓ j-x‖ ≤ 1 := by
  have hℓ0 : 0 < ℓ := zero_lt_one.trans_le hℓ
  simp only [packetAxisShift,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hε (mul_pos hn hℓ0).le)]
  simp only [EuclideanSpace.basisFun_apply,PiLp.norm_single,norm_one,mul_one]
  have he : n*(ε/(n*ℓ)) = ε/ℓ := by field_simp
  simpa only [mul_one,he] using (div_le_one hℓ0).mpr (hε1.trans hℓ)

lemma packetAxisShift_covector {n ε ℓ : ℝ} (hn : n ≠ 0) (hℓ : ℓ ≠ 0)
    (x : NormalWaveSpace) (j : Fin 3) (β : NormalWaveSpace →L[ℝ] ℝ) :
    n*β (packetAxisShift x n ε ℓ j-x) = ε/ℓ*β (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
  simp only [packetAxisShift,add_sub_cancel_left,map_smul,smul_eq_mul]
  field_simp

lemma profile_exp_close (φ : NormalWaveSpace → ℝ) {H n : ℝ} (hn : 0 ≤ n)
    (hH : 0 ≤ H) (x y : NormalWaveSpace) (hstep : n*‖y-x‖ ≤ 1)
    (hφ : |φ y-φ x| ≤ H*‖y-x‖) :
    Real.exp (n*φ y) ≤ Real.exp H*Real.exp (n*φ x) := by
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hφ) hn
  have hh' := mul_le_mul_of_nonneg_left hstep hH
  nlinarith

lemma quartic_tail_budget_eventually {a B δ c : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, B*(t^12*Real.exp (-a*t^2)) ≤ δ*c := by
  have ht := (tendsto_const_nhds (x := B) (f := atTop)).mul (polynomial_gaussian_tail_tendsto ha)
  have ht' : Tendsto (fun t : ℝ => B*(t^12*Real.exp (-a*t^2))) atTop (𝓝 0) := by simpa using ht
  filter_upwards [ht'.eventually_lt_const (mul_pos hδ hc)] with t ht using ht.le
end YauCounterexamples
end

end OAI

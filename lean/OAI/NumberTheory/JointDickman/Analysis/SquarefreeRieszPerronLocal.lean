import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszMovingHankel
import OAI.NumberTheory.JointDickman.Analysis.ZetaPerronScale

namespace OAI

/-! # The local expansion at the concrete Perron cutoff -/
namespace JointDickman
open Filter Asymptotics Finset
open scoped Topology

noncomputable def perronLogScaleWidth (A L : ℝ) : ℝ :=
  perronScaleWidth A (L^(1/10:ℝ))

theorem perronScaleWidth_tendsto_zero {A : ℝ} (hA : 0 < A) :
    Tendsto (perronScaleWidth A) atTop (𝓝 0) := by
  have hlim : Tendsto (fun q : ℝ => A/(4*q)) atTop (𝓝 0) := by
    simpa only [div_div,id_eq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => A/4) atTop (𝓝 (A/4))).div_atTop tendsto_id
  apply squeeze_zero' (Eventually.of_forall (fun q => (perronScaleWidth_pos hA (q := q)).le)) _ hlim
  filter_upwards [eventually_ge_atTop (2:ℝ)] with q hq
  exact perronScaleWidth_upper hA.le hq

theorem perronLogScaleWidth_tendsto_zero {A : ℝ} (hA : 0 < A) :
    Tendsto (perronLogScaleWidth A) atTop (𝓝 0) :=
  (perronScaleWidth_tendsto_zero hA).comp (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10))

theorem perronLogScaleWidth_growth {A : ℝ} (hA : 0 < A) :
    ∀ᶠ L in atTop, (A/4096)*L^(1/10:ℝ) ≤ L*perronLogScaleWidth A L/2 := by
  filter_upwards [eventually_ge_atTop (0:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/10)).eventually (eventually_ge_atTop (2:ℝ))] with L hL hq
  have he : (L^(1/10:ℝ))^10 = L := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hL]
    norm_num
  have h := perronScaleWidth_mul_lower hA hq
  rw [he] at h
  change (A/4096)*L^(1/10:ℝ) ≤ L*perronScaleWidth A (L^(1/10:ℝ))/2
  linarith

theorem squarefreeRiesz_perron_local_expansion {z A : ℝ}
    (hz : 0 < z) (hz1 : z < 1) (hA : 0 < A) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z / 2 ∧ 0 < c 0 ∧
      ∀ H : ℕ, (fun L : ℝ => squarefreeRieszLocalHankel z (perronLogScaleWidth A L) L -
        ∑ j ∈ range (H+1), c j*L^(z-1-j)) =O[atTop] (fun L => L^(z-2-H)) := by
  exact squarefreeRiesz_moving_hankel_expansion hz hz1
    (div_pos hA (by norm_num)) (by norm_num : (0:ℝ) < 1/10)
    (Eventually.of_forall (fun L => (perronScaleWidth_pos hA (q := L^(1/10:ℝ))).le))
    (perronLogScaleWidth_tendsto_zero hA) (perronLogScaleWidth_growth hA)

end JointDickman

end OAI

import OAI.Analysis.LipschitzHilbert.Phase.AngularLossMotion
import OAI.Analysis.LipschitzHilbert.Phase.SourcePhaseParameters

namespace OAI

/-! The quantitative small factors in predictable motion. Fixed powers
and constants are absorbed only after the packet and weight estimates. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

theorem source_moving_weight_factor_le {a δ : ℝ}
    (ha1 : a ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1)) ≤
      (Real.exp 1*(1+2*Real.exp 1))*δ := by
  have he : Real.exp (a*δ) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right ha1 hδ0
    linarith
  have hnonneg : 0 ≤ δ+(Real.exp (2*δ)-1) := by
    have := Real.one_le_exp (show 0 ≤ 2*δ by positivity)
    linarith
  have hrel := relative_loss_factor_le hδ0 hδ1
  calc
    _ ≤ Real.exp 1*(δ+(Real.exp (2*δ)-1)) :=
      mul_le_mul_of_nonneg_right he hnonneg
    _ ≤ Real.exp 1*(δ+(2*Real.exp 1)*δ) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hrel) (Real.exp_pos 1).le
    _ = _ := by ring

/-- The two summation-by-parts errors have a common inverse-square-root
factor as soon as their independent packet and weight bounds do. -/
theorem source_predictable_coefficient_le {V A E d W J G : ℝ}
    (hV : 0 ≤ V) (hA : 0 ≤ A) (hE : 0 ≤ E) (hW : 0 ≤ W) (hG : 1 ≤ G)
    (hd : d ≤ W/Real.sqrt G) (hpacket : E ≤ J/Real.sqrt G) :
    V*((1+d)*E+d*A) ≤ (V*((1+W)*J+W*A))/Real.sqrt G := by
  have hs : 1 ≤ Real.sqrt G := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    simpa using hG
  have hdW : d ≤ W := hd.trans (div_le_self hW hs)
  have hfirst : (1+d)*E ≤ (1+W)*(J/Real.sqrt G) := by
    calc
      _ ≤ (1+W)*E := mul_le_mul_of_nonneg_right (by linarith) hE
      _ ≤ _ := mul_le_mul_of_nonneg_left hpacket (by positivity)
  calc
    _ ≤ V*((1+W)*(J/Real.sqrt G)+(W/Real.sqrt G)*A) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hfirst (mul_le_mul_of_nonneg_right hd hA)) hV
    _ = _ := by ring

/-- Every fixed polynomial prefactor in the exact source motion bounds
is dominated by a quarter-power gain of the actual rounded dyadic step. -/
theorem eventually_source_polynomial_motion (C p : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      C*L^p/Real.sqrt (SourceParameters.step L) ≤
        SourceParameters.step L^(-(1/4:ℝ)) := by
  have hsub := eventually_source_subpower_amplitude (p+1) (1/4) (by norm_num)
  filter_upwards [hsub, eventually_ge_atTop (max 1 C)] with L hL hlarge
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hCL : C ≤ L := (le_max_right _ _).trans hlarge
  have hpower : L^(p+1) ≤ SourceParameters.step L^(1/4:ℝ) := by
    have h := hL 1 1 (by norm_num) (by norm_num) (by simp; positivity)
    have hn : 0 ≤ L^(p+1) := Real.rpow_nonneg hL0.le _
    norm_num at h
    linarith
  have hpoly : C*L^p ≤ SourceParameters.step L^(1/4:ℝ) := by
    calc
      _ ≤ L*L^p := mul_le_mul_of_nonneg_right hCL (Real.rpow_nonneg hL0.le _)
      _ = L^(p+1) := by rw [Real.rpow_add hL0, Real.rpow_one]; ring
      _ ≤ _ := hpower
  calc
    _ ≤ SourceParameters.step L^(1/4:ℝ)/Real.sqrt (SourceParameters.step L) :=
      div_le_div_of_nonneg_right hpoly (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_sub (SourceParameters.step_pos L)]
      norm_num

end LipschitzHilbert

end

end OAI

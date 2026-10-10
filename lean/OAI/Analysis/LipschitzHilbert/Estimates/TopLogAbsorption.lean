import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

/-! The logarithmic endpoint factor is absorbed by the spare decay of
an actual top weight, without any positive lower cutoff on that weight. -/

noncomputable section
namespace LipschitzHilbert

theorem bounded_weight_rpow_le_linear {h C q : ℝ} {d : ℕ}
    (hh : 0 < h) (hC : 1 ≤ C) (hhC : h ≤ C)
    (hq : 1 ≤ q) (hqd : q ≤ (d : ℝ)+1) :
    h^q ≤ C^d*h := by
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hbase : h^(q-1) ≤ C^d := by
    apply (Real.rpow_le_rpow hh.le hhC (by linarith : 0 ≤ q-1)).trans
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hC (by linarith)
  calc
    h^q = h^((q-1)+1) := by congr 1; ring
    _ = h^(q-1)*h := by rw [Real.rpow_add hh, Real.rpow_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hbase hh.le

/-- Small weights have no logarithmic singularity after the available
polynomial decay is used. The total mass enters only through its logarithm. -/
theorem top_log_absorption {h S C Q q : ℝ} {d : ℕ}
    (hh : 0 < h) (hS : 0 < S) (hC : 1 ≤ C) (hhC : h ≤ C)
    (hQ : 0 ≤ Q) (hq : 2 ≤ q) (hqd : q ≤ (d : ℝ)+1) :
    h^q * (1+Q*Real.log (S/h)) ≤
      C^d * (1+Q*(Real.log (max 1 S)+1))*h := by
  have hp := bounded_weight_rpow_le_linear hh hC hhC (by linarith : 1 ≤ q) hqd
  have hp' := bounded_weight_rpow_le_linear hh hC hhC (by linarith : 1 ≤ q-1)
    (by linarith : q-1 ≤ (d : ℝ)+1)
  have hlog : Real.log (S/h) ≤ Real.log (max 1 S)+h⁻¹ := by
    have hSlog : Real.log S ≤ Real.log (max 1 S) := Real.log_le_log hS (le_max_right _ _)
    have hhlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hh)
    rw [Real.log_inv] at hhlog
    rw [Real.log_div hS.ne' hh.ne']
    linarith
  have hlog0 : 0 ≤ Real.log (max 1 S) := Real.log_nonneg (le_max_left _ _)
  have hinv : h^q*h⁻¹ = h^(q-1) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hh]
    congr 1
  calc
    _ ≤ h^q * (1+Q*(Real.log (max 1 S)+h⁻¹)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hh.le _)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hQ)
    _ = h^q*(1+Q*Real.log (max 1 S))+Q*h^(q-1) := by
      rw [← hinv]
      ring
    _ ≤ (C^d*h)*(1+Q*Real.log (max 1 S))+Q*(C^d*h) :=
      add_le_add (mul_le_mul_of_nonneg_right hp (by positivity))
        (mul_le_mul_of_nonneg_left hp' hQ)
    _ = _ := by ring

/-- The concentration envelope and endpoint normalization combine to a
bound linear in the top weight, even when that weight tends to zero. -/
theorem normalized_top_amplitude_bound {E : Type*} [NormedAddCommGroup E]
    (v : E) {h n0 nM S C B Q a : ℝ}
    (hh : 0 < h) (hhn : h ≤ nM) (hn : nM ≤ n0) (hnS : n0 ≤ S)
    (hC : 1 ≤ C) (hhC : h ≤ C) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hv : ‖v‖ ≤ (h^(-a)*(1+Q*Real.log (n0/nM)))*(B*h^8)) :
    ‖v‖ ≤ (C^8*B*(1+Q*(Real.log (max 1 S)+1)))*h := by
  have hnM : 0 < nM := hh.trans_le hhn
  have hn0 : 0 < n0 := hnM.trans_le hn
  have hS : 0 < S := hn0.trans_le hnS
  have hratio : n0/nM ≤ S/h := by
    calc
      _ ≤ S/nM := div_le_div_of_nonneg_right hnS hnM.le
      _ ≤ _ := div_le_div_of_nonneg_left hS.le hh hhn
  have hlog : Real.log (n0/nM) ≤ Real.log (S/h) :=
    Real.log_le_log (div_pos hn0 hnM) hratio
  have hpw : h^(-a)*h^8 = h^(8-a) := by
    rw [← Real.rpow_natCast h 8, ← Real.rpow_add hh]
    congr 1
    norm_num
    ring
  have hbound := top_log_absorption (d := 8) hh hS hC hhC hQ
    (by linarith : 2 ≤ 8-a) (by norm_num; linarith : 8-a ≤ (8 : ℝ)+1)
  calc
    ‖v‖ ≤ (h^(-a)*(1+Q*Real.log (n0/nM)))*(B*h^8) := hv
    _ = B*(h^(8-a)*(1+Q*Real.log (n0/nM))) := by rw [← hpw]; ring
    _ ≤ B*(h^(8-a)*(1+Q*Real.log (S/h))) := by
      gcongr
    _ ≤ B*(C^8*(1+Q*(Real.log (max 1 S)+1))*h) :=
      mul_le_mul_of_nonneg_left hbound hB
    _ = _ := by ring

/-- The four powers retained in the manuscript's individual-top bound. -/
theorem top_log_absorption_four {h S C Q a : ℝ}
    (hh : 0 < h) (hS : 0 < S) (hC : 1 ≤ C) (hhC : h ≤ C)
    (hQ : 0 ≤ Q) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    h^(8-a) * (1+Q*Real.log (S/h)) ≤
      C^8 * (1+Q*(Real.log (max 1 S)+1))*h^4 := by
  have hb := top_log_absorption (q := 5-a) (d := 8) hh hS hC hhC hQ
    (by linarith) (by norm_num; linarith)
  have heq : h^(8-a) = h^3*h^(5-a) := by
    rw [← Real.rpow_natCast h 3, ← Real.rpow_add hh]
    congr 1
    norm_num
    ring
  calc
    _ = h^3*(h^(5-a)*(1+Q*Real.log (S/h))) := by rw [heq]; ring
    _ ≤ h^3*(C^8*(1+Q*(Real.log (max 1 S)+1))*h) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- The normalized source amplitude retains four powers of the top
weight, uniformly down to arbitrarily small positive weights. -/
theorem normalized_top_amplitude_bound_four {E : Type*} [NormedAddCommGroup E]
    (v : E) {h n0 nM S C B Q a : ℝ}
    (hh : 0 < h) (hhn : h ≤ nM) (hn : nM ≤ n0) (hnS : n0 ≤ S)
    (hC : 1 ≤ C) (hhC : h ≤ C) (hB : 0 ≤ B) (hQ : 0 ≤ Q)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hv : ‖v‖ ≤ (h^(-a)*(1+Q*Real.log (n0/nM)))*(B*h^8)) :
    ‖v‖ ≤ (C^8*B*(1+Q*(Real.log (max 1 S)+1)))*h^4 := by
  have hnM : 0 < nM := hh.trans_le hhn
  have hn0 : 0 < n0 := hnM.trans_le hn
  have hS : 0 < S := hn0.trans_le hnS
  have hlog : Real.log (n0/nM) ≤ Real.log (S/h) :=
    Real.log_le_log (div_pos hn0 hnM)
      ((div_le_div_of_nonneg_right hnS hnM.le).trans
        (div_le_div_of_nonneg_left hS.le hh hhn))
  have hpw : h^(-a)*h^8 = h^(8-a) := by
    rw [← Real.rpow_natCast h 8, ← Real.rpow_add hh]
    congr 1
    norm_num
    ring
  have hb := top_log_absorption_four hh hS hC hhC hQ ha0 ha1
  calc
    ‖v‖ ≤ (h^(-a)*(1+Q*Real.log (n0/nM)))*(B*h^8) := hv
    _ = B*(h^(8-a)*(1+Q*Real.log (n0/nM))) := by rw [← hpw]; ring
    _ ≤ B*(h^(8-a)*(1+Q*Real.log (S/h))) := by gcongr
    _ ≤ B*(C^8*(1+Q*(Real.log (max 1 S)+1))*h^4) :=
      mul_le_mul_of_nonneg_left hb hB
    _ = _ := by ring

end LipschitzHilbert

end

end OAI

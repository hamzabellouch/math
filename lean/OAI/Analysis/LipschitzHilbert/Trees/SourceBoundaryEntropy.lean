import OAI.Analysis.LipschitzHilbert.Estimates.TopLogAbsorption
import OAI.Analysis.LipschitzHilbert.Trees.SourceSnapshotSize

namespace OAI

/-! The remaining logarithmic boundary loss is linear in the actual top
weight after its available eight powers are used. Summation has no
factor depending on the number of tops. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- A positive bounded weight absorbs the logarithmic ratio to the
ambient mass, with a constant independent of the small weight. -/
theorem boundary_weight_entropy_le {h n C : ℝ}
    (hh : 0 < h) (hhn : h ≤ n) (hC : 1 ≤ C) (hhC : h ≤ C) :
    h^8*Real.log (n/h) ≤ C^7*h*(1+Real.log (max 1 n)) := by
  have hn : 0 < n := hh.trans_le hhn
  have hlog : Real.log (n/h) ≤ Real.log (max 1 n)+h⁻¹ := by
    have hnlog := Real.log_le_log hn (le_max_right 1 n)
    have hhlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hh)
    rw [Real.log_inv] at hhlog
    rw [Real.log_div hn.ne' hh.ne']
    linarith
  have hlog0 : 0 ≤ Real.log (max 1 n) := Real.log_nonneg (le_max_left 1 n)
  have hp8 : h^8 ≤ C^7*h := by
    simpa only [Real.rpow_ofNat] using
      (bounded_weight_rpow_le_linear (q := (8:ℝ)) (d := 7) hh hC hhC
        (by norm_num) (by norm_num))
  have hp7 : h^7 ≤ C^7*h := by
    simpa only [Real.rpow_ofNat] using
      (bounded_weight_rpow_le_linear (q := (7:ℝ)) (d := 7) hh hC hhC
        (by norm_num) (by norm_num))
  have hinv : h^8*h⁻¹ = h^7 := by
    rw [show h^8 = h^7*h by ring,mul_assoc,mul_inv_cancel₀ hh.ne',mul_one]
  calc
    h^8*Real.log (n/h) ≤ h^8*(Real.log (max 1 n)+h⁻¹) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = h^8*Real.log (max 1 n)+h^7 := by rw [mul_add,hinv]
    _ ≤ (C^7*h)*Real.log (max 1 n)+C^7*h :=
      add_le_add (mul_le_mul_of_nonneg_right hp8 hlog0) hp7
    _ = C^7*h*(1+Real.log (max 1 n)) := by ring

theorem boundary_weight_entropy_sum_le {ι : Type*} (tops : Finset ι) (h : ι → ℝ)
    {C : ℝ} (hC : 1 ≤ C) (hpos : ∀ t ∈ tops, 0 < h t)
    (hbound : ∀ t ∈ tops, h t ≤ C) :
    (∑ t ∈ tops, h t^8*Real.log ((∑ u ∈ tops, h u)/h t)) ≤
      C^7*(1+Real.log (max 1 (∑ u ∈ tops, h u)))*(∑ t ∈ tops, h t) := by
  classical
  calc
    _ ≤ ∑ t ∈ tops, C^7*h t*(1+Real.log (max 1 (∑ u ∈ tops, h u))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact boundary_weight_entropy_le (hpos t ht)
        (Finset.single_le_sum (fun u hu => (hpos u hu).le) ht) hC (hbound t ht)
    _ = _ := by rw [←Finset.sum_mul,←Finset.mul_sum]; ring

namespace SlopeBox

theorem weight_boundary_entropy_le (T : SlopeBox) {Kw D n : ℝ}
    (hKw : 0 < Kw) (hD : 0 ≤ D) (z : ℝ×ℝ) (hn : T.weight Kw D z ≤ n) :
    (T.weight Kw D z)^8*Real.log (n/T.weight Kw D z) ≤
      ((2:ℝ)^D)^7*T.weight Kw D z*(1+Real.log (max 1 n)) :=
  boundary_weight_entropy_le (T.weight_pos hKw D z) hn
    (Real.one_le_rpow (by norm_num) hD) (T.weight_le_two_pow hKw hD z)

end SlopeBox

theorem top_weight_boundary_entropy_sum_le {ι : Type*}
    (tops : Finset ι) (T : ι → SlopeBox) {Kw D : ℝ}
    (hKw : 0 < Kw) (hD : 0 ≤ D) (z : ℝ×ℝ) :
    (∑ t ∈ tops, ((T t).weight Kw D z)^8*
      Real.log ((∑ u ∈ tops, (T u).weight Kw D z)/(T t).weight Kw D z)) ≤
      ((2:ℝ)^D)^7*(1+Real.log (max 1 (∑ u ∈ tops, (T u).weight Kw D z)))*
        (∑ t ∈ tops, (T t).weight Kw D z) :=
  boundary_weight_entropy_sum_le tops (fun t => (T t).weight Kw D z)
    (Real.one_le_rpow (by norm_num) hD) (fun t _ => (T t).weight_pos hKw D z)
    (fun t _ => (T t).weight_le_two_pow hKw hD z)

/-- The common good-set logarithmic mass bound turns the entropy sum
into the same linear top mass used by the plane estimates. -/
theorem top_weight_boundary_entropy_sum_le_log_bound {ι : Type*}
    (tops : Finset ι) (T : ι → SlopeBox) {Kw D H : ℝ}
    (hKw : 0 < Kw) (hD : 0 ≤ D) (z : ℝ×ℝ)
    (hlog : Real.log (max 1 (∑ u ∈ tops, (T u).weight Kw D z)) ≤ H) :
    (∑ t ∈ tops, ((T t).weight Kw D z)^8*
      Real.log ((∑ u ∈ tops, (T u).weight Kw D z)/(T t).weight Kw D z)) ≤
      ((2:ℝ)^D)^7*(1+H)*(∑ t ∈ tops, (T t).weight Kw D z) := by
  apply (top_weight_boundary_entropy_sum_le tops T hKw hD z).trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  · exact Finset.sum_nonneg (fun t _ => ((T t).weight_pos hKw D z).le)

end LipschitzHilbert

end

end OAI

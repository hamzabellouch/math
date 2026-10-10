import OAI.NumberTheory.TotientAsymptotic.ScaledConcentration
import OAI.NumberTheory.TotientAsymptotic.EnlargementTail
import OAI.NumberTheory.TotientAsymptotic.BandComparison

namespace OAI

/-! Uniform phase-band comparison and the actual coordinate scaling bounds. -/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace TotientAsymptotic

lemma fullSimplexCenter_eq_fordBandScale {x : ℝ} {i : ℕ} (hi : i < m x) :
    fullSimplexCenter (m x) (B x) i = fordBandScale x i := by
  have hmR : (m x : ℝ) ≠ 0 := by exact_mod_cast (show m x ≠ 0 by omega)
  unfold fullSimplexCenter fordBandScale
  rw [Nat.cast_sub hi.le]
  field_simp

lemma phase_band_center_close : ∀ᶠ x : ℝ in atTop, ∀ i < m x,
    (99/100 : ℝ)*fullSimplexCenter (m x) (B x) i ≤ bandScale x i ∧
      bandScale x i ≤ (101/100 : ℝ)*fullSimplexCenter (m x) (B x) i := by
  filter_upwards [B_tendsto.eventually (eventually_gt_atTop (1 : ℝ)),
    Metric.tendsto_nhds.mp bandCenterRatio_tendsto (1/200) (by norm_num)] with x hB hx
  intro i hi
  have ht := (bandScale_pos hi).le
  rw [fullSimplexCenter_eq_fordBandScale hi, fordBandScale_eq_ratio_mul hB hi]
  have hh : |bandCenterRatio x-1| < (1/200 : ℝ) := by
    simpa only [Real.dist_eq] using hx
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hh
  constructor <;> nlinarith

def fullBoxScale (x : ℝ) (H : ℕ) (i : Fin (L x H)) : ℝ :=
  enlargementScale (fun r => 1+simplexBoxError 4 (m x-r)) i

lemma fullBoxScale_one_le (x : ℝ) (H : ℕ) (i : Fin (L x H)) :
    1 ≤ fullBoxScale x H i := by
  unfold fullBoxScale enlargementScale
  apply Finset.one_le_prod₀
  intro r _
  linarith [simplexBoxError_nonneg (by norm_num : (0 : ℝ)≤4) (m x-r)]

lemma fullBoxScale_prefix_close : ∀ᶠ H : ℕ in atTop, ∀ x : ℝ,
    H ≤ m x → ∀ i : Fin (L x H), i.val < R x H → fullBoxScale x H i ≤ (102/100 : ℝ) := by
  have ht := (Real.continuous_exp.tendsto (0 : ℝ)).comp (simplexBoxTail_tendsto 4)
  filter_upwards [ht.eventually (eventually_lt_nhds (by norm_num : Real.exp (0 : ℝ)<102/100))]
    with H hH
  intro x hHm i hi
  apply (reverse_enlargement_coordinate hHm (simplexBoxError 4)
    (simplexBoxError_nonneg (by norm_num)) (summable_simplexBoxError_weighted 4) i hi).trans
  rw [← simplexBoxTail_eq_tsum]
  exact hH.le

lemma fullBoxScale_jacobian {x : ℝ} {H : ℕ} (hPm : P H ≤ m x) :
    (∏ i : Fin (L x H), fullBoxScale x H i) ≤ Real.exp (simplexBoxTail 4 (P H)) := by
  change (∏ i : Fin (m x-P H), enlargementScale
    (fun r => 1+simplexBoxError 4 (m x-r)) i) ≤ _
  have hh := reverse_enlargement_jacobian hPm (simplexBoxError 4)
    (simplexBoxError_nonneg (by norm_num)) (summable_simplexBoxError_weighted 4)
  rw [← simplexBoxTail_eq_tsum] at hh
  exact hh


end TotientAsymptotic

end

end OAI

import OAI.NumberTheory.Ostmann.Conclusion.ScaleReserves
import OAI.NumberTheory.Ostmann.Construction.LogCellPrimePrior

namespace OAI

noncomputable section
open Filter
namespace Ostmann.Construction

def giantNormalizationCost (G : ℝ) : ℝ := -Real.log (logCellMass G ∅)

lemma exp_neg_giantNormalizationCost (G : ℝ) (hZ : 0<logCellMass G ∅) :
    Real.exp (-giantNormalizationCost G)=logCellMass G ∅ := by
  simp only [giantNormalizationCost,neg_neg,Real.exp_log hZ]

lemma exp_giantNormalizationCost (G : ℝ) (hZ : 0<logCellMass G ∅) :
    Real.exp (giantNormalizationCost G)=(logCellMass G ∅)⁻¹ := by
  rw [giantNormalizationCost,Real.exp_neg,Real.exp_log hZ]

theorem giantNormalizationCost_linear_eventually :
    ∀ᶠ L:ℝ in atTop,∀c:ℝ,
      Real.exp ((1/20:ℝ)*L)-2≤c → c≤Real.exp ((9/10:ℝ)*L)+2 →
      0<logCellMass c ∅ ∧ giantNormalizationCost c≤(9/10:ℝ)*L+Real.log 6 := by
  obtain ⟨T₀,hT₀⟩ := eventually_atTop.mp logCell_normalization_eventually
  filter_upwards [eventually_ge_atTop (0:ℝ),eventually_ge_atTop (20*(T₀+3))]
    with L hL hlarge
  intro c hlo hhi
  have hc : T₀≤c := by
    have he := Real.add_one_le_exp ((1/20:ℝ)*L)
    linarith
  obtain ⟨hZ,hZlo,hZhi⟩ := hT₀ c hc ∅ (by simp)
  have he1 : 1≤Real.exp ((9/10:ℝ)*L) := Real.one_le_exp (by positivity)
  have hinv : (logCellMass c ∅)⁻¹≤6*Real.exp ((9/10:ℝ)*L) := by
    linarith
  have hlog := Real.log_le_log (inv_pos.mpr hZ) hinv
  rw [Real.log_inv,Real.log_mul (by norm_num : (6:ℝ)≠0) (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  exact ⟨hZ,by simpa only [giantNormalizationCost,add_comm] using hlog⟩

theorem giantNormalizationCost_bulk_reserve_eventually {k : ℕ} (hk : 0<k) :
    ∀ᶠ L:ℝ in atTop,∀c:ℝ,
      Real.exp ((1/20:ℝ)*L)-2≤c → c≤Real.exp ((9/10:ℝ)*L)+2 →
      giantNormalizationCost c+Real.log 2≤(Conclusion.bulkSize k L:ℝ) := by
  filter_upwards [giantNormalizationCost_linear_eventually,eventually_ge_atTop (0:ℝ),
    eventually_ge_atTop (10*(Real.log 6+Real.log 2+2))] with L hcost hL hlarge
  intro c hlo hhi
  have hcg := (hcost c hlo hhi).2
  have hbulk := (Conclusion.bulkSize_bounds k hL).1
  have hk1 : 1≤Conclusion.bulkScale k := Conclusion.bulkScale_one_le hk
  have hscale := mul_le_mul_of_nonneg_right hk1 hL
  nlinarith

end Ostmann.Construction

end

end OAI

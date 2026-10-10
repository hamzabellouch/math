import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! Normalize the three deletion costs by the exact padding and tuple
masses. The rare-site term uses only S*V ≥ 1. -/

namespace TwoPointCorrelations

lemma normalize_three_deletion_costs
    (F pad deg rare S V T α β δ ep ed er : ℝ)
    (hS : 1 ≤ S) (hV : 1 ≤ V) (hδ : 0 ≤ δ)
    (hF : F ≤ pad + deg + rare)
    (hpad : pad ≤ S * V * T * α + ep)
    (hdeg : deg ≤ S * V * T * β + ed)
    (hrare : rare ≤ δ + er) :
    F / (S * V) ≤ T * (α + β) + δ + (ep + ed + er) / (S * V) := by
  have hSV : 1 ≤ S * V := by nlinarith
  have hSVpos : 0 < S * V := by linarith
  have hrare' : δ ≤ S * V * δ := by nlinarith
  have hb : F ≤ S * V * (T * (α + β) + δ) + (ep + ed + er) := by nlinarith
  calc
    _ ≤ (S * V * (T * (α + β) + δ) + (ep + ed + er)) / (S * V) :=
      div_le_div_of_nonneg_right hb hSVpos.le
    _ = _ := by rw [add_div, mul_div_cancel_left₀ _ hSVpos.ne']

lemma normalize_endpoint_deletion_costs
    (F pad deg rare S V T α β δ ep ed er : ℝ)
    (hS : 1 ≤ S) (hV : 1 ≤ V) (hδ : 0 ≤ δ)
    (hF : F ≤ 2 * (pad + deg + rare))
    (hpad : pad ≤ S * V * T * α + ep)
    (hdeg : deg ≤ S * V * T * β + ed)
    (hrare : rare ≤ δ + er) :
    F / (S * V) ≤ 2 * (T * (α + β) + δ + (ep + ed + er) / (S * V)) := by
  have hSVpos : 0 < S * V := mul_pos (by linarith) (by linarith)
  have hb := normalize_three_deletion_costs (pad + deg + rare) pad deg rare S V T α β δ ep ed er
    hS hV hδ le_rfl hpad hdeg hrare
  calc
    _ ≤ (2 * (pad + deg + rare)) / (S * V) := div_le_div_of_nonneg_right hF hSVpos.le
    _ = 2 * ((pad + deg + rare) / (S * V)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)

end TwoPointCorrelations

end OAI

import OAI.Analysis.LipschitzHilbert.Trees.SourceShearedEnvelopeEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedTreeEnergy

namespace OAI

/-! The quadratic reciprocal weight used for the packed short packets
matches the long-tree product weight up to an absolute factor. -/
noncomputable section
namespace LipschitzHilbert

private theorem line_weight_product_lower (a L x : ℝ) (hL : 0<L) :
    1≤4*(lineEnvelope a L 1 x*polynomialWeight a (2*L) 1 x) := by
  have hbase : 0<1+((x-a)/L)^2 := by positivity
  have he : (x-a)^2/(2*L)^2=((x-a)/L)^2/4 := by
    field_simp
    ring
  have hb : 1+((x-a)/L)^2≤4*(1+(x-a)^2/(2*L)^2) := by
    rw [he]
    nlinarith [sq_nonneg ((x-a)/L)]
  have hd := (le_div_iff₀ hbase).mpr (show
    1*(1+((x-a)/L)^2)≤4*(1+(x-a)^2/(2*L)^2) by simpa only [one_mul] using hb)
  calc
    1 ≤4*(1+(x-a)^2/(2*L)^2)/(1+((x-a)/L)^2) := hd
    _ = _ := by
      simp only [lineEnvelope,polynomialWeight,pow_one,div_eq_mul_inv]
      ring

theorem envelope_tree_weight_lower (a b L W t : ℝ) (hL : 0<L) (hW : 0<W)
    (z : ℝ×ℝ) :
    1≤16*(shearedTopReciprocal a b L W t z*
      treeProductPolynomial a (b-t*a) L W t z) := by
  have hx := line_weight_product_lower a L z.1 hL
  have hy := line_weight_product_lower (b-t*a) W (z.2-t*z.1) hW
  have h := mul_le_mul hx hy (by norm_num : (0:ℝ)≤1) (le_trans (by norm_num) hx)
  calc
    1 = 1*1 := by ring
    _ ≤ _ := h
    _ = _ := by
      dsimp only [shearedTopReciprocal,topReciprocalWeight,treeProductPolynomial]
      ring

end LipschitzHilbert

end

end OAI

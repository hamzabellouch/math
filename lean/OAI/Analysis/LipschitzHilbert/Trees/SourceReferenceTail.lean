import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceBounds
import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialMomentBound
import OAI.Analysis.LipschitzHilbert.Estimates.MomentSuperlevel

namespace OAI

/-! Natural-order forms of the exact reference moments. The moment grid
may have fixed binary branching, independent of the source angular step. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.SourceLatticePacket

def referenceSquareMomentBase (B : ℝ) (grid : FiniteLineGrid) : ℝ :=
  16*((((grid.branching:ℝ)+2)*(2*LinePacketFamily.squareMeanConstant B+
    48*(4*Real.pi)^4))/Real.log (3/2)+LinePacketFamily.squareMeanConstant B+1)

theorem referenceSquareMomentBase_pos (B : ℝ) (grid : FiniteLineGrid) (hB : 0 ≤ B) :
    0 < referenceSquareMomentBase B grid := by
  have hR : 0 ≤ LinePacketFamily.squareMeanConstant B := by
    unfold LinePacketFamily.squareMeanConstant
    positivity
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  unfold referenceSquareMomentBase
  positivity

theorem reference_square_moment_majorant (B : ℝ) (grid : FiniteLineGrid) (hB : 0 ≤ B)
    (n : ℕ) (hn : 1 ≤ n) :
    referenceSquareMomentCost B grid (2*(n:ℝ)) ≤
      ENNReal.ofReal ((referenceSquareMomentBase B grid*(n:ℝ))^n) := by
  have hR : 0 ≤ LinePacketFamily.squareMeanConstant B := by
    unfold LinePacketFamily.squareMeanConstant
    positivity
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have hQ : 0 ≤ (((grid.branching:ℝ)+2)*(2*LinePacketFamily.squareMeanConstant B+
      48*(4*Real.pi)^4))/Real.log (3/2) := by positivity
  have h := ennreal_polynomial_moment_majorant _ _ hQ hR n hn
  simpa only [referenceSquareMomentCost,referenceSquareMomentBase,
    show 2*(n:ℝ)/2 = n by ring,mul_div_assoc] using h

theorem reference_variation_moment_majorant (M C B : ℝ) (grid : FiniteLineGrid)
    (hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n) :
    referenceVariationMomentCost M C B grid n ≤
      ENNReal.ofReal ((lineMomentBase C (M*C^2*B+1) grid.branching*(n:ℝ))^n) := by
  exact line_moment_expression_le C (M*C^2*B+1) grid.branching
    hC (Nat.cast_nonneg _) n hn

theorem reference_variation_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ) (hF : Measurable F)
    (M C B : ℝ) (grid : FiniteLineGrid) (hC : 0 ≤ C) (n : ℕ) (hn : 1 ≤ n)
    (hm : (∫⁻ x, (ENNReal.ofReal |F x|)^(n:ℝ) ∂μ) ≤
      referenceVariationMomentCost M C B grid n*μ univ) :
    μ {x | 4*(lineMomentBase C (M*C^2*B+1) grid.branching*(n:ℝ)) ≤ |F x|} ≤
      (1/4:ℝ≥0∞)^n*μ univ := by
  have hbase := lineMomentBase_pos C (M*C^2*B+1) grid.branching hC (Nat.cast_nonneg _)
  have hnR : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  apply moment_superlevel_quarter μ F hF n _ (mul_pos hbase hnR)
  simpa only [ENNReal.rpow_natCast,ENNReal.ofReal_pow (mul_pos hbase hnR).le]
    using hm.trans (mul_le_mul' (reference_variation_moment_majorant M C B grid hC n hn) le_rfl)

/-- The square reference quantity has an exponential tail for its square;
this avoids any loss from taking roots in the moment estimate. -/
theorem reference_square_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ) (hF : Measurable F)
    (B : ℝ) (grid : FiniteLineGrid) (hB : 0 ≤ B) (n : ℕ) (hn : 1 ≤ n)
    (hm : (∫⁻ x, (ENNReal.ofReal |F x|)^(2*(n:ℝ)) ∂μ) ≤
      referenceSquareMomentCost B grid (2*(n:ℝ))*μ univ) :
    μ {x | 4*(referenceSquareMomentBase B grid*(n:ℝ)) ≤ (F x)^2} ≤
      (1/4:ℝ≥0∞)^n*μ univ := by
  have hbase := referenceSquareMomentBase_pos B grid hB
  have hnR : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hpow (x : X) : (ENNReal.ofReal |(F x)^2|)^n =
      (ENNReal.ofReal |F x|)^(2*(n:ℝ)) := by
    have hncast : 2*(n:ℝ) = ((2*n:ℕ):ℝ) := by push_cast; ring
    rw [hncast,ENNReal.rpow_natCast,abs_pow,ENNReal.ofReal_pow (abs_nonneg _),pow_mul]
  have hm' : (∫⁻ x, (ENNReal.ofReal |(F x)^2|)^n ∂μ) ≤
      (ENNReal.ofReal (referenceSquareMomentBase B grid*(n:ℝ)))^n*μ univ := by
    simp_rw [hpow]
    rw [← ENNReal.ofReal_pow (mul_pos hbase hnR).le]
    exact hm.trans (mul_le_mul' (reference_square_moment_majorant B grid hB n hn) le_rfl)
  have ht := moment_superlevel_quarter μ (fun x => (F x)^2) (hF.pow_const 2) n
    (referenceSquareMomentBase B grid*(n:ℝ)) (mul_pos hbase hnR) (μ univ) hm'
  simpa only [abs_sq] using ht

end LipschitzHilbert.SourceLatticePacket

end

end OAI

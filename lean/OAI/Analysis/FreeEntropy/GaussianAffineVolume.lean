import OAI.Analysis.FreeEntropy.FlowSeparation

namespace OAI

universe u1

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace FiniteEntropySeparation
 theorem gaussian_affine_volume {ι : Type u1} [Fintype ι] (a : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0<r)
    (s : Set (EuclideanSpace ℝ ι))
    (h : (1/2:ℝ≥0∞) ≤ productGaussian ι ((fun x => a+r • WithLp.toLp 2 x) ⁻¹' s)) :
    ENNReal.ofReal (r^(Fintype.card ι)/2) ≤ volume s := by
  have hp : productGaussian ι ((fun x => a+r • WithLp.toLp 2 x) ⁻¹' s) ≤
      ENNReal.ofReal ((r^(Fintype.card ι))⁻¹)*volume s := by
    have hh := productGaussian_toLp_le_volume ι ((fun x => a+r • x) ⁻¹' s)
    have he : ((fun x : EuclideanSpace ℝ ι => a+r • x) ⁻¹' s) =
        (fun x => r • x) ⁻¹' ((fun x => a+x) ⁻¹' s) := rfl
    rw [he,Measure.addHaar_preimage_smul volume hr.ne', measure_preimage_add] at hh
    simpa only [finrank_euclideanSpace,Set.preimage_preimage,Function.comp_def,abs_of_pos (inv_pos.mpr (pow_pos hr _))] using hh
  have hm : ENNReal.ofReal (r^(Fintype.card ι)) * (1/2:ℝ≥0∞) ≤
      ENNReal.ofReal (r^(Fintype.card ι)) * (ENNReal.ofReal ((r^(Fintype.card ι))⁻¹)*volume s) := by
    gcongr; exact h.trans hp
  rw [← mul_assoc,← ENNReal.ofReal_mul (pow_nonneg hr.le _),mul_inv_cancel₀ (pow_ne_zero _ hr.ne'),ENNReal.ofReal_one,one_mul] at hm
  simpa only [div_eq_mul_inv,ENNReal.ofReal_mul (pow_nonneg hr.le _),ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_ofNat,one_mul] using hm
end FiniteEntropySeparation

end

end OAI

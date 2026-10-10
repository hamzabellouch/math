import OAI.NumberTheory.TotientAsymptotic.PrefixWeights
import OAI.NumberTheory.TotientAsymptotic.PublishedConcentration

namespace OAI

/-! Transporting the coordinate events through the exact simplex map. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixSimplexMap_det (N : ℕ) :
    LinearMap.det (prefixSimplexMap N) = ∏ i : Fin N, g (i.val+1) := by
  rw [prefixSimplexMap, LinearMap.det_comp, prefixLinear_det, mul_one, weightedScale_det]

lemma prefixSimplexMap_det_pos (N : ℕ) : 0 < LinearMap.det (prefixSimplexMap N) := by
  rw [prefixSimplexMap_det]
  exact Finset.prod_pos (fun i _ => g_pos _)

lemma prefixSimplexMap_preimage (N : ℕ) (B : ℝ) :
    prefixRegion N B 0 0 = prefixSimplexMap N ⁻¹' standardSimplex N B := by
  rw [prefixRegion_eq_simplex_preimage]
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero,
    weightedSimplex_eq_preimage]
  rfl

lemma volume_prefixSimplexMap_preimage (N : ℕ) (T : Set (Fin N → ℝ))
    (hT : MeasurableSet T) :
    volume (prefixSimplexMap N ⁻¹' T) =
      ENNReal.ofReal ((LinearMap.det (prefixSimplexMap N))⁻¹)*volume T := by
  rw [← Measure.map_apply (prefixSimplexMap N).continuous_of_finiteDimensional.measurable hT,
    Real.map_linearMap_volume_pi_eq_smul_volume_pi (prefixSimplexMap_det_pos N).ne',
    Measure.smul_apply, smul_eq_mul, abs_of_pos (inv_pos.mpr (prefixSimplexMap_det_pos N))]

lemma prefixSimplexMap_ford_ratio (N : ℕ) (B : ℝ) (u : Fin (N+2) → ℝ)
    (i : Fin (N+2)) :
    (∑ j, prefixWeight (N+2) i j*prefixSimplexMap (N+2) u j)/
        (B*(((N+2-i.val:ℕ):ℝ)-1)/(N+2:ℝ)) = u i/fordSimplexCenter N B i := by
  rw [← prefixSimplexMap_coordinate]
  have hi : i.val ≤ N+2 := by omega
  have hden : fordSimplexCenter N B i = rho^(i.val+1)*
      (B*(((N+2-i.val:ℕ):ℝ)-1)/(N+2:ℝ)) := by
    unfold fordSimplexCenter
    rw [Nat.cast_sub hi]
    push_cast
    field_simp
    ring
  rw [hden, div_div]

lemma prefixSimplexMap_bad_preimage (N : ℕ) (B : ℝ) (i : Fin (N+2)) :
    prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i =
      prefixSimplexMap (N+2) ⁻¹'
        (standardSimplex (N+2) B ∩
          {v | (1/40:ℝ) < |(∑ j, prefixWeight (N+2) i j*v j)/
            (B*(((N+2-i.val:ℕ):ℝ)-1)/(N+2:ℝ))-1|}) := by
  rw [prefixSimplexMap_preimage]
  ext u
  simp only [Set.mem_inter_iff, Set.mem_preimage, fordCoordinateBad, Set.mem_ofPred_eq,
    prefixSimplexMap_ford_ratio]

end TotientAsymptotic

end

end OAI

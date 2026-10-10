import OAI.NumberTheory.TotientAsymptotic.PrefixSimplexMap
import OAI.NumberTheory.TotientAsymptotic.SimplexConcentration

namespace OAI

/-! Unconditional coordinate concentration for the exact prefix simplex. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

lemma prefixSimplexMap_transfer (N : ℕ) (B R : ℝ) (T : Set (Fin N → ℝ))
    (hT : MeasurableSet T)
    (hbound : (volume T).toReal ≤ R*(volume (standardSimplex N B)).toReal) :
    (volume (prefixSimplexMap N ⁻¹' T)).toReal ≤
      R*(volume (prefixRegion N B 0 0)).toReal := by
  rw [volume_prefixSimplexMap_preimage N T hT, ENNReal.toReal_mul,
    prefixSimplexMap_preimage, volume_prefixSimplexMap_preimage N _
      (measurableSet_standardSimplex N B), ENNReal.toReal_mul]
  exact (mul_le_mul_of_nonneg_left hbound ENNReal.toReal_nonneg).trans_eq (by ring)

theorem prefix_coordinate_concentration_unconditional :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ N : ℕ, ∀ B : ℝ, 0 < B → ∀ i : Fin (N+2), i.val < N →
      (volume (prefixRegion (N+2) B 0 0 ∩ fordCoordinateBad N B i)).toReal ≤
        C*Real.exp (-c*(N+2-(i.val+1) : ℕ))*(volume (prefixRegion (N+2) B 0 0)).toReal := by
  obtain ⟨M,K,hM,hK,hweights⟩ := prefixWeight_bounds
  let s := concentrationTilt M
  refine ⟨2*Real.exp (3*s*(K+1)),s/100,by positivity,
    div_pos (concentrationTilt_pos hM) (by norm_num),?_⟩
  intro N B hB i hi
  obtain ⟨hw,hS,hQ⟩ := hweights (N+2) i
  have hm : 2 ≤ N+2-i.val := by omega
  have hmN : N+2-i.val ≤ N+2 := Nat.sub_le _ _
  have hc := volume_simplex_fixed_deviation M K hM hK.le (N+2) (N+2-i.val) hm hmN B hB
    (prefixWeight (N+2) i) hw hS hQ
  have he : N+2-i.val-1 = N+2-(i.val+1) := by omega
  rw [he] at hc
  rw [prefixSimplexMap_bad_preimage]
  apply prefixSimplexMap_transfer
  · apply (measurableSet_standardSimplex _ _).inter
    apply measurableSet_lt measurable_const
    fun_prop
  · simpa only [Nat.cast_add,Nat.cast_ofNat] using hc

end TotientAsymptotic

end

end OAI

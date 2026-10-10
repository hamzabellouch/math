import OAI.Analysis.Pureness.Divisibility.SourceRankLimit

namespace OAI
namespace CuntzPureness
open Filter Topology
open scoped NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

noncomputable def positivePower (a : A) (r : ℝ≥0) : A := CFC.nnrpow a r

lemma starAlgHom_positive (φ : A →⋆ₐ[ℂ] B) (a : A) (ha : 0 ≤ a) : 0 ≤ φ a := by
  have hs : star (CFC.sqrt a) * CFC.sqrt a = a := by
    rw [(CFC.sqrt_nonneg a).star_eq, CFC.sqrt_mul_sqrt_self a ha]
  rw [← hs, map_mul, map_star]
  exact star_mul_self_nonneg _

lemma positivePower_map (φ : A →⋆ₐ[ℂ] B) (a : A) (ha : 0 ≤ a)
    (r : ℝ≥0) (hr : 0 < r) : positivePower (φ a) r = φ (positivePower a r) := by
  have hb := starAlgHom_positive φ a ha
  simp only [positivePower, CFC.nnrpow_eq_pow,
    CFC.nnrpow_eq_cfcₙ_real a r ha, CFC.nnrpow_eq_cfcₙ_real (φ a) r hb]
  have hf0 : (0 : ℝ) ^ (r : ℝ) = 0 := Real.zero_rpow (by exact_mod_cast hr.ne')
  rw [cfcₙ_eq_cfc (hf0 := hf0), cfcₙ_eq_cfc (hf0 := hf0)]
  exact (φ.map_cfc _ a (Real.continuous_rpow_const (by positivity)).continuousOn
    (map_continuous φ) ha.isSelfAdjoint hb.isSelfAdjoint).symm

lemma positivePower_trace_tendsto (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (τ.functional (positivePower a (((n : ℝ≥0) + 1)⁻¹))).re)
      atTop (𝓝 (normalizedRootRank τ a).toReal) := by
  have hfinite : normalizedRootRank τ a ≠ ∞ :=
    ne_of_lt ((normalizedRootRank_le_one τ a ha).trans_lt ENNReal.one_lt_top)
  have ht := (ENNReal.tendsto_toReal hfinite).comp (source_root_trace_tendsto_rank τ a ha)
  exact ht.congr' (Eventually.of_forall fun n => ENNReal.toReal_ofReal
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg CFC.nnrpow_nonneg)).1)
end CuntzPureness

end OAI

import OAI.Analysis.Pureness.Completion.CompletedRankExhaustion
import OAI.Analysis.Pureness.Operators.OrthogonalRanks

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
open scoped ComplexOrder ENNReal NNReal

section Unital
variable {E : Type*} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

lemma positive_nnrpow_nat_succ (a : E) (ha : 0 ≤ a) (n : ℕ) :
    CFC.nnrpow a ((n : ℝ≥0) + 1) = a ^ (n + 1) := by
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_add, zero_add, pow_one, CFC.nnrpow_eq_pow] using CFC.nnrpow_one a ha
  | succ n ih =>
    have he : ((n + 1 : ℕ) : ℝ≥0) + 1 = ((n : ℝ≥0) + 1) + 1 := by norm_cast
    rw [he, CFC.nnrpow_eq_pow, CFC.nnrpow_add (by positivity) (by positivity), CFC.nnrpow_one a ha]
    rw [← CFC.nnrpow_eq_pow, ih]
    exact (pow_succ a (n + 1)).symm

lemma positive_nnrpow_mem_hereditary (a : E) (ha : 0 ≤ a) (r : ℝ≥0) :
    CFC.nnrpow a r ∈ hereditaryCarrier a := by
  change CFC.nnrpow a r ∈ hereditarySubalgebra a ha
  rw [CFC.nnrpow_eq_pow, CFC.nnrpow_eq_cfcₙ_real a r ha]
  exact cfcₙ_mem _ (show a ∈ hereditarySubalgebra a ha from self_mem_hereditary a ha)

omit [PartialOrder E] [StarOrderedRing E] in
lemma orthogonal_add_pow_succ (a b : E) (hab : a * b = 0) (hba : b * a = 0) (n : ℕ) :
    (a + b) ^ (n + 1) = a ^ (n + 1) + b ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (a + b) (n + 1), ih, add_mul, mul_add, mul_add]
    have h1 : a ^ (n + 1) * b = 0 := by rw [pow_succ, mul_assoc, hab, mul_zero]
    have h2 : b ^ (n + 1) * a = 0 := by rw [pow_succ, mul_assoc, hba, mul_zero]
    rw [h1, h2, add_zero, zero_add, ← pow_succ, ← pow_succ]

lemma positive_reciprocal_power_add (a b : E) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a * b = 0) (j : ℕ) :
    CFC.nnrpow (a + b) (((j : ℝ≥0) + 1)⁻¹) =
      CFC.nnrpow a (((j : ℝ≥0) + 1)⁻¹) + CFC.nnrpow b (((j : ℝ≥0) + 1)⁻¹) := by
  let r : ℝ≥0 := ((j : ℝ≥0) + 1)⁻¹
  have hp : CFC.nnrpow a r * CFC.nnrpow b r = 0 :=
    hereditary_mul_eq_zero (positive_nnrpow_mem_hereditary a ha r)
      (positive_nnrpow_mem_hereditary b hb r) hab
  have hpa : 0 ≤ CFC.nnrpow a r := CFC.nnrpow_nonneg
  have hpb : 0 ≤ CFC.nnrpow b r := CFC.nnrpow_nonneg
  have hq : CFC.nnrpow b r * CFC.nnrpow a r = 0 := by
    simpa only [star_mul, hpa.star_eq, hpb.star_eq, star_zero] using congrArg star hp
  apply (CFC.nnrpow_inv_eq (a + b) _ (by positivity : (j : ℝ≥0) + 1 ≠ 0)
    (add_nonneg ha hb) (add_nonneg CFC.nnrpow_nonneg CFC.nnrpow_nonneg)).mpr
  rw [← CFC.nnrpow_eq_pow, positive_nnrpow_nat_succ _ (add_nonneg CFC.nnrpow_nonneg CFC.nnrpow_nonneg)]
  change (CFC.nnrpow a r + CFC.nnrpow b r) ^ (j + 1) = a + b
  rw [orthogonal_add_pow_succ _ _ hp hq j,
    ← positive_nnrpow_nat_succ _ hpa j, ← positive_nnrpow_nat_succ _ hpb j]
  simp only [r, CFC.nnrpow_eq_pow, CFC.nnrpow_nnrpow,
    inv_mul_cancel₀ (by positivity : (j : ℝ≥0) + 1 ≠ 0), CFC.nnrpow_one a ha, CFC.nnrpow_one b hb]
end Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma completed_reciprocal_power_add (a b : CornerCompletion A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a * b = 0) (j : ℕ) :
    CFC.nnrpow (a + b) (((j : ℝ≥0) + 1)⁻¹) =
      CFC.nnrpow a (((j : ℝ≥0) + 1)⁻¹) + CFC.nnrpow b (((j : ℝ≥0) + 1)⁻¹) := by
  let φ := Unitization.inrNonUnitalStarAlgHom ℂ (CornerCompletion A)
  apply Unitization.inr_injective (R := ℂ)
  change φ (CFC.nnrpow (a + b) _) = φ (CFC.nnrpow a _ + CFC.nnrpow b _)
  rw [map_add, ← nonUnital_nnrpow_map φ Unitization.continuous_inr _ (add_nonneg ha hb) _ (by positivity),
    map_add, ← nonUnital_nnrpow_map φ Unitization.continuous_inr a ha _ (by positivity),
    ← nonUnital_nnrpow_map φ Unitization.continuous_inr b hb _ (by positivity)]
  exact positive_reciprocal_power_add _ _ (Unitization.inr_nonneg_iff.mpr ha)
    (Unitization.inr_nonneg_iff.mpr hb) (by rw [← Unitization.inr_mul, hab, Unitization.inr_zero]) j

theorem completedRootRank_add_orthogonal (τ : TracialState A) (a b : CornerCompletion A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = 0) :
    completedRootRank τ (a + b) = completedRootRank τ a + completedRootRank τ b := by
  apply tendsto_nhds_unique (completed_root_trace_tendsto_rank τ (a + b) (add_nonneg ha hb))
  convert (completed_root_trace_tendsto_rank τ a ha).add (completed_root_trace_tendsto_rank τ b hb) using 1
  funext j
  rw [completed_reciprocal_power_add a b ha hb hab j]
  exact completedDiagonalWeight_add τ (CFC.nnrpow a (((j : ℝ≥0) + 1)⁻¹))
    (CFC.nnrpow b (((j : ℝ≥0) + 1)⁻¹)) CFC.nnrpow_nonneg CFC.nnrpow_nonneg
end CuntzPureness

end

end OAI

import OAI.Analysis.BoundedHochschild.NormalOrderIntervals
import OAI.Analysis.BoundedHochschild.OrthogonalProjectionSums

namespace OAI

/-!
# Positivity detected on projections

The spectral approximation step in Ringrose, *Lectures on the trace in a
finite von Neumann algebra*, Lemma 3.5. Dyadic spectral projections suffice.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma positive_contraction_eval_nonneg_of_projection_nonneg
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : StrongDual ℂ M)
    (hreal : ∀ a : M, IsSelfAdjoint a → (F a).im = 0)
    (hproj : ∀ p : M, IsStarProjection p → 0 ≤ F p)
    (a : M) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 0 ≤ F a := by
  have hbound (n : ℕ) : ∀ b : M, 0 ≤ b → b ≤ 1 →
      -((1 / 2 : ℝ) ^ n) * ‖F‖ ≤ (F b).re := by
    induction n with
    | zero =>
        intro b hb0 hb1
        have hn : ‖F b‖ ≤ ‖F‖ := (F.le_opNorm b).trans
          (mul_le_of_le_one_right (norm_nonneg _) ((CStarAlgebra.norm_le_one_iff_of_nonneg b hb0).mpr hb1))
        have hr := Complex.abs_re_le_norm (F b)
        simp only [pow_zero, neg_mul, one_mul]
        linarith [neg_le_abs (F b).re]
    | succ n ih =>
        intro b hb0 hb1
        obtain ⟨p, hp, hlow, hupp⟩ := HochschildSakai.exists_dyadic_projection e b hb0 hb1
        have hh := ih ((2 : ℝ) • b - p) hlow hupp
        have he : F ((2 : ℝ) • b - p) = (2 : ℝ) • F b - F p := by simp
        rw [he] at hh
        have hp0 : 0 ≤ (F p).re := (Complex.nonneg_iff.mp (hproj p hp)).1
        simp at hh
        have hpow : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by simp [one_div]
        rw [← hpow] at hh
        rw [pow_succ]
        nlinarith
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hreal a ha0.isSelfAdjoint).symm⟩
  have ht : Tendsto (fun n : ℕ => -((1 / 2 : ℝ) ^ n) * ‖F‖) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : (1 / 2 : ℝ) < 1)).neg.mul_const ‖F‖)
  exact le_of_tendsto ht (Eventually.of_forall fun n => hbound n a ha0 ha1)

/-- A bounded hermitian functional nonnegative on projections is positive. -/
theorem eval_nonneg_of_projection_nonneg (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (F : StrongDual ℂ M) (hreal : ∀ a : M, IsSelfAdjoint a → (F a).im = 0)
    (hproj : ∀ p : M, IsStarProjection p → 0 ≤ F p) :
    ∀ a : M, 0 ≤ a → 0 ≤ F a := by
  intro a ha
  let t : ℝ := ‖a‖ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  let c : M := t⁻¹ • a
  have hc0 : 0 ≤ c := smul_nonneg (inv_nonneg.mpr ht.le) ha
  have hcn : ‖c‖ ≤ 1 := by
    rw [show c = t⁻¹ • a from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_le_one₀ ht).mpr (by dsimp [t]; linarith)
  have hc1 : c ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg c hc0).mp hcn
  have hh := smul_nonneg ht.le
    (positive_contraction_eval_nonneg_of_projection_nonneg e F hreal hproj c hc0 hc1)
  have hca : t • c = a := by
    dsimp [c]
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have he : (t : ℝ) • F c = F a := by
    calc
      (t : ℝ) • F c = F ((t : ℝ) • c) := by simp
      _ = F a := congrArg F hca
  rwa [he] at hh

end KadisonRingrose
end BoundedHochschild

end

end OAI

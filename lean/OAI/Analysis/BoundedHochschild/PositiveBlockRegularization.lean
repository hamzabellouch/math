import OAI.Analysis.BoundedHochschild.PositiveBlockTransfer

namespace OAI

/-! Remove strict positivity of the scalar block entries by norm limits. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {D A B : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma starAlgHom_real_one (ρ : D →⋆ₐ[ℂ] A) (r : ℝ) :
    ρ (r • (1 : D)) = r • (1 : A) := by
  rw [← Complex.coe_smul, map_smul, map_one, Complex.coe_smul]

lemma positive_real_one (r : ℝ) (hr : 0 < r) : IsStrictlyPositive (r • (1 : D)) := by
  refine ⟨smul_nonneg hr.le zero_le_one, ?_⟩
  rw [← Algebra.algebraMap_eq_smul_one]
  exact (isUnit_iff_ne_zero.mpr hr.ne').map (algebraMap ℝ D)

omit [PartialOrder A] [StarOrderedRing A] in
lemma positiveBlock_add_real_one (p q x : A) (r : ℝ) :
    positiveBlock (p + r • 1) (q + r • 1) x = positiveBlock p q x + r • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [positiveBlock, diag, offdiag, add_comm]

theorem positiveBlock_transfer (ρ : D →⋆ₐ[ℂ] A) (σ : D →⋆ₐ[ℂ] B)
    (T : A →ₗ[ℂ] B) (hT : ∀ a, ‖T a‖ ≤ ‖a‖)
    (hmodule : ∀ d e a, T (ρ d * a * ρ e) = σ d * T a * σ e)
    (p q : D) (hp : 0 ≤ p) (hq : 0 ≤ q) (a : A)
    (ha : 0 ≤ positiveBlock (ρ p) (ρ q) a) :
    0 ≤ positiveBlock (σ p) (σ q) (T a) := by
  have heps (r : ℝ) (hr : 0 < r) :
      0 ≤ positiveBlock (σ p) (σ q) (T a) + r • 1 := by
    have h := positiveBlock_transfer_strict ρ σ T hT hmodule
      (p + r • 1) (q + r • 1)
      (IsStrictlyPositive.nonneg_add hp (positive_real_one r hr))
      (IsStrictlyPositive.nonneg_add hq (positive_real_one r hr)) a
    simp only [map_add, starAlgHom_real_one, positiveBlock_add_real_one] at h
    exact h (add_nonneg ha (smul_nonneg hr.le zero_le_one))
  have ht : Tendsto (fun n : ℕ => positiveBlock (σ p) (σ q) (T a) +
      (1 / ((n : ℝ) + 1)) • 1) atTop (𝓝 (positiveBlock (σ p) (σ q) (T a))) := by
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul
        (tendsto_const_nhds (x := (1 : Mat B)))))
  exact ge_of_tendsto' ht (fun n => heps _ (by positivity))

end BoundedHochschild.KadisonRingrose

end

end OAI

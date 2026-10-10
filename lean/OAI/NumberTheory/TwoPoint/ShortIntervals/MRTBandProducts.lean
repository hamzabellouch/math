import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandEuler

namespace OAI

/-! Multiplication of the band bounds preserves a single square-root
Euler factor.  Pairwise disjointness removes every repeated prime cost. -/

namespace TwoPointCorrelations

open Complex Finset
open scoped Classical

lemma mrt_euler_block_bound {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1 / 2) :
    ‖∏ i ∈ S, (1 - z i)⁻¹‖ ≤
      Real.sqrt ‖∏ i ∈ S, (1 - z i)⁻¹‖ *
        Real.exp ((∑ i ∈ S, (‖z i‖ + ‖z i‖ ^ 2)) / 2) := by
  let L : ℂ := ∑ i ∈ S, Complex.log (1 - z i)⁻¹
  have he : Complex.exp L = ∏ i ∈ S, (1 - z i)⁻¹ := mrt_euler_block_exp S z hz
  have hnorm : ‖∏ i ∈ S, (1 - z i)⁻¹‖ = Real.exp L.re := by
    rw [← he, Complex.norm_exp]
  have hL : L.re ≤ ∑ i ∈ S, (‖z i‖ + ‖z i‖ ^ 2) :=
    (Complex.re_le_norm L).trans ((norm_sum_le _ _).trans
      (sum_le_sum fun i hi => mrt_local_euler_log_bound (hz i hi)))
  rw [hnorm, ← Real.exp_half, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

theorem mrt_band_product_bound {ι κ : Type*} (R : Finset ι) (J : Finset κ)
    (P : κ → Finset ι) (z : ι → ℂ)
    (hR : ∀ i ∈ R, ‖z i‖ ≤ 1 / 2)
    (hP : ∀ j ∈ J, ∀ i ∈ P j, ‖z i‖ ≤ 1 / 2) :
    ‖(∏ i ∈ R, (1 - z i)⁻¹) *
        ∏ j ∈ J, ((∏ i ∈ P j, (1 - z i)⁻¹) - 1)‖ ≤
      Real.sqrt ‖(∏ i ∈ R, (1 - z i)⁻¹) * ∏ j ∈ J, ∏ i ∈ P j, (1 - z i)⁻¹‖ *
        Real.exp (((∑ i ∈ R, (‖z i‖ + ‖z i‖ ^ 2)) +
          ∑ j ∈ J, ∑ i ∈ P j, (‖z i‖ + ‖z i‖ ^ 2)) / 2) := by
  have hb := mrt_euler_block_bound R z hR
  have hp := prod_le_prod₀
    (fun j (_ : j ∈ J) => norm_nonneg ((∏ i ∈ P j, (1 - z i)⁻¹) - 1))
    (fun j hj => mrt_euler_block_difference_bound (P j) z (hP j hj))
  rw [norm_mul, norm_prod (f := fun j => (∏ i ∈ P j, (1 - z i)⁻¹) - 1)]
  calc
    _ ≤ (Real.sqrt ‖∏ i ∈ R, (1 - z i)⁻¹‖ *
          Real.exp ((∑ i ∈ R, (‖z i‖ + ‖z i‖ ^ 2)) / 2)) *
        ∏ j ∈ J, (Real.sqrt ‖∏ i ∈ P j, (1 - z i)⁻¹‖ *
          Real.exp ((∑ i ∈ P j, (‖z i‖ + ‖z i‖ ^ 2)) / 2)) := by
      exact mul_le_mul hb hp (prod_nonneg fun _ _ => norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
    _ = _ := by
      rw [prod_mul_distrib, ← Real.sqrt_prod J (fun _ _ => norm_nonneg _),
        ← Real.exp_sum, ← norm_prod, norm_mul, Real.sqrt_mul (norm_nonneg _),
        ← sum_div]
      rw [show ((∑ i ∈ R, (‖z i‖ + ‖z i‖ ^ 2)) +
          ∑ j ∈ J, ∑ i ∈ P j, (‖z i‖ + ‖z i‖ ^ 2)) / 2 =
          (∑ i ∈ R, (‖z i‖ + ‖z i‖ ^ 2)) / 2 +
          (∑ j ∈ J, ∑ i ∈ P j, (‖z i‖ + ‖z i‖ ^ 2)) / 2 by ring,
        Real.exp_add]
      ring

/-- The complement and all disjoint bands partition the original finite
Euler product, so the cost contains each prime exactly once. -/
theorem mrt_partitioned_euler_bound {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (J : Finset κ)
    (P : κ → Finset ι) (z : ι → ℂ)
    (hsub : ∀ j ∈ J, P j ⊆ S) (hdis : Set.PairwiseDisjoint (J : Set κ) P)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1 / 2) :
    ‖(∏ i ∈ S \ J.biUnion P, (1 - z i)⁻¹) *
        ∏ j ∈ J, ((∏ i ∈ P j, (1 - z i)⁻¹) - 1)‖ ≤
      Real.sqrt ‖∏ i ∈ S, (1 - z i)⁻¹‖ *
        Real.exp ((∑ i ∈ S, (‖z i‖ + ‖z i‖ ^ 2)) / 2) := by
  have hU : J.biUnion P ⊆ S := by
    intro i hi
    obtain ⟨j, hj, hip⟩ := mem_biUnion.mp hi
    exact hsub j hj hip
  have hp := mrt_band_product_bound (S \ J.biUnion P) J P z
    (fun i hi => hz i (mem_sdiff.mp hi).1) (fun j hj i hi => hz i (hsub j hj hi))
  rw [← prod_biUnion hdis, prod_sdiff hU, ← sum_biUnion hdis, sum_sdiff hU] at hp
  exact hp

end TwoPointCorrelations

end OAI

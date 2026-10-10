import OAI.Analysis.FreeEntropy.MatrixBilinear

namespace OAI

universe u1

noncomputable section
open scoped ComplexConjugate
open Finset Metric Set
namespace FiniteEntropySeparation
 variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
 theorem norm_le_of_unit_inner (z : E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v : E, ‖v‖ = 1 → ‖inner ℂ v z‖ ≤ C) : ‖z‖ ≤ C := by
  by_cases hz : z=0
  · simpa [hz] using hC
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hv : ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 := by rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
  have hh := h ((‖z‖⁻¹ : ℝ) • z) hv
  simpa [inner_smul_real_left, norm_smul, inner_self_eq_norm_sq_to_K, norm_pow,
    Real.norm_eq_abs, abs_inv, abs_norm, sq, ← mul_assoc, inv_mul_cancel₀ hn] using hh
 theorem opNorm_le_of_bilinear (T : E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ‖inner ℂ x (T y)‖ ≤ C) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hC
  intro y hy
  exact norm_le_of_unit_inner _ hC (fun x hx => h x y hx hy)
 theorem bilinear_net_bound (T : E →L[ℂ] E) (s : Finset E)
    (hs : ∀ x ∈ s, ‖x‖ = 1)
    (hcov : ∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, dist x y ≤ 1/4)
    {M : ℝ} (hM : 0 ≤ M) (hB : ∀ x ∈ s, ∀ y ∈ s, ‖inner ℂ x (T y)‖ ≤ M) : ‖T‖ ≤ 2*M := by
  have hb : ‖T‖ ≤ M + ‖T‖/2 := by
    apply opNorm_le_of_bilinear T (by positivity)
    intro x y hx hy
    obtain ⟨u,hu,hxu⟩ := hcov x hx
    obtain ⟨v,hv,hyv⟩ := hcov y hy
    have he : inner ℂ x (T y) = inner ℂ u (T v) + inner ℂ (x-u) (T y) + inner ℂ u (T (y-v)) := by
      simp only [map_sub, inner_sub_left, inner_sub_right]; abel
    have h1 : ‖inner ℂ (x-u) (T y)‖ ≤ ‖T‖/4 := by
      calc
        _ ≤ ‖x-u‖*‖T y‖ := norm_inner_le_norm _ _
        _ ≤ (1/4)*(‖T‖*‖y‖) := mul_le_mul (by simpa [dist_eq_norm] using hxu) (T.le_opNorm y) (norm_nonneg _) (by norm_num)
        _ = _ := by rw [hy]; ring
    have h2 : ‖inner ℂ u (T (y-v))‖ ≤ ‖T‖/4 := by
      calc
        _ ≤ ‖u‖*‖T (y-v)‖ := norm_inner_le_norm _ _
        _ ≤ ‖u‖*(‖T‖*‖y-v‖) := mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
        _ ≤ 1*(‖T‖*(1/4)) := by rw [hs u hu]; gcongr; simpa [dist_eq_norm] using hyv
        _ = _ := by ring
    rw [he]
    exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hB u hu v hv) h1)) h2)).trans_eq (by ring)
  linarith
 theorem sphere_finite_net [FiniteDimensional ℝ E] :
    ∃ s : Finset E, (∀ x ∈ s, ‖x‖ = 1) ∧
    (∀ x : E, ‖x‖ = 1 → ∃ y ∈ s, dist x y ≤ 1/4) ∧
    (s.card : ℝ) ≤ 9^Module.finrank ℝ E := by
  obtain ⟨s,hs,hc,hb⟩ := compact_finite_net (sphere (0:E) 1) (isCompact_sphere 0 1)
    (R := 1) (ε := 1/4) (by norm_num) (by norm_num) (by intro x hx; exact (mem_sphere_zero_iff_norm.mp hx).le)
  refine ⟨s,?_,?_,?_⟩
  · intro x hx; exact mem_sphere_zero_iff_norm.mp (hs x hx)
  · intro x hx; exact hc x (mem_sphere_zero_iff_norm.mpr hx)
  · norm_num at hb ⊢; exact hb
end FiniteEntropySeparation

end

end OAI

import OAI.Analysis.CircleDomains.Sobolev.PriorityLocalDerivative

namespace OAI

/-! The horizontal interpolation differs from the original derivative
only by its cutoff-gradient error and the original gradient on the union
of cutoff supports. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem priorityInfiniteValue_derivative_error
    (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (X : E → ℝ) {p : E} {B : ℝ}
    (hX : DifferentiableAt ℝ X p) (hXb : ‖X p‖ ≤ B)
    (hχ : ∀ n, DifferentiableAt ℝ (χ n) p ∧ χ n p ∈ Icc (0 : ℝ) 1)
    (hc : ∀ n, ‖c n‖ ≤ B)
    (hs : Summable (fun n => ‖fderiv ℝ (χ n) p‖))
    (hz : ∃ N : ℕ, ∀ᶠ q in 𝓝 p, ∀ n, N ≤ n → χ n q = 0) :
    ‖fderiv ℝ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) p -
      fderiv ℝ X p‖ ≤
      2*B*(∑' n, ‖fderiv ℝ (χ n) p‖) +
        (⋃ n, support (χ n)).indicator (fun q => ‖fderiv ℝ X q‖) p := by
  classical
  let a : ℝ := ∑' n, priorityWeight (fun j => χ j p) n
  have ha := priorityWeight_tsum_mem_unit (fun n => (hχ n).2)
  have hbound := (priorityInfiniteValue_local_derivative χ c X hX hXb hχ hc hs hz).2
  let D := fderiv ℝ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) p
  let V := fderiv ℝ X p
  have he : D-V = (D-(1-a) • V) + (-a) • V := by module
  have hnorm : ‖D-V‖ ≤ ‖D-(1-a) • V‖ + a*‖V‖ := by
    rw [he]
    apply (norm_add_le _ _).trans_eq
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ha.1]
  have hrem : a*‖V‖ ≤ (⋃ n, support (χ n)).indicator (fun q => ‖fderiv ℝ X q‖) p := by
    by_cases hp : p ∈ ⋃ n, support (χ n)
    · rw [indicator_of_mem hp]
      exact (mul_le_mul_of_nonneg_right ha.2 (norm_nonneg V)).trans_eq (one_mul _)
    · have hpz (n : ℕ) : χ n p = 0 := by
        by_contra hn
        exact hp (mem_iUnion.mpr ⟨n, hn⟩)
      have haz : a = 0 := by
        simp only [a, priorityWeight, hpz, zero_mul, tsum_zero]
      rw [haz, zero_mul, indicator_of_notMem hp]
  exact hnorm.trans (add_le_add hbound hrem)

end CircleDomainRigidity

end

end OAI

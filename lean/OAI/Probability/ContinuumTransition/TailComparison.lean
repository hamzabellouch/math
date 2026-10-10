import OAI.Probability.ContinuumTransition.GibbsMonotonicity

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem physical_log_tail_bound {t β : ℝ} (ht : 0 < t) (hβ : 0 < β)
    {σ τ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hτ : ∀ n, 0 ≤ τ n) (hR : ∀ n, 1 ≤ R n)
    (hs : Summable σ) (hτs : Summable τ)
    (hsmall : 2197*t*kernelHeight*(∑' n, (σ n+τ n)) ≤ (t^2/8)/8) (h L : ℝ) :
    0 ≤ Real.log (grandPartition (physicalProfile t (fun n => σ n+τ n) R) t β h L)-
      Real.log (grandPartition (physicalProfile t σ R) t β h L) ∧
    Real.log (grandPartition (physicalProfile t (fun n => σ n+τ n) R) t β h L)-
      Real.log (grandPartition (physicalProfile t σ R) t β h L) ≤
      β*(momentConstant t β (t*h)/2)*(cubeCells L).card*(2197*t*kernelHeight*(∑' n, τ n)) := by
  let U := fun x y : Space => physicalProfile t σ R ‖x-y‖
  let V := fun x y : Space => physicalProfile t (fun n => σ n+τ n) R ‖x-y‖
  have hστ (n : ℕ) : 0 ≤ σ n+τ n := add_nonneg (hσ n) (hτ n)
  have hVU (x y : Space) : V x y ≤ U x y := physicalProfile_add_mono ht.le hσ hτ hR hs hτs ‖x-y‖
  have hV := physical_cellLowerBound ht.le hστ hR (hs.add hτs)
  have hU := hV.mono hVU
  have hUm := measurable_physical_interaction t hσ hR hs
  have hVm := measurable_physical_interaction t hστ hR (hs.add hτs)
  have hfin : volume (cube L) ≠ ⊤ := by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hUF := cellLowerBound_gibbs_finite ht.le hβ.le hστ hR (hs.add hτs) hsmall hU hUm hfin (t*h)
  have hVF := cellLowerBound_gibbs_finite ht.le hβ.le hστ hR (hs.add hτs) hsmall hV hVm hfin (t*h)
  have hmono := grandIntegral_gibbs_antitone hβ.le hVU (t*h) (measurableSet_cube L) hVF hUF
  have hZ := grandIntegral_gibbs_pos U β (t*h) (cube L) hUF.summable
  have hnonneg := sub_nonneg.mpr (Real.log_le_log hZ hmono)
  have hbound := modified_log_grand_comparison ht hβ hστ hR (hs.add hτs) hsmall hU hV hUm hVm
    (fun x y => by simp only [U, norm_sub_rev])
    (fun x y => by simp only [norm_sub_rev]) hVU (t*h) L
    (fun k l => physicalCoupling t τ R k l)
    (fun k l => physicalCoupling_nonneg ht.le hτ hR k l)
    (fun k l x y _ _ hx hy => by
      dsimp only [U, V]
      rw [physicalProfile_add_diff t hσ hτ hR hs hτs]
      have hh := attraction_le_mixedEnvelope ht.le hτ hR hτs x y
      simpa only [hx, hy, physicalCoupling] using hh)
  have hrow := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (cubeCells L))) =>
    physicalCoupling_row ht.le hτ hR hτs (fun l : cubeCells L => (l : Lattice)) Subtype.val_injective k)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe] at hrow
  have hh := hbound.trans (mul_le_mul_of_nonneg_left hrow
    (mul_nonneg hβ.le (div_nonneg (momentConstant_pos ht hβ (t*h)).le (by norm_num))))
  dsimp only [U, V] at hnonneg hh
  rw [grandIntegral_radial, grandIntegral_radial] at hnonneg hh
  refine ⟨hnonneg, ?_⟩
  simpa only [mul_assoc] using hh

end ContinuumTemperature
end

end OAI

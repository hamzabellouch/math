import OAI.Probability.ContinuumTransition.ModifiedFinite

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem cellLowerBound_exponential_moment_bound {t β : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(∑' n, σ n) ≤ (t^2/8)/8)
    {V : Space → Space → ℝ} (hV : CellLowerBound t σ R V)
    (hVm : Measurable (Function.uncurry V)) (hVsym : ∀ x y, V x y = V y x)
    (h L : ℝ) (z : cubeCells L) :
    grandIntegral (momentFamily (gibbsFamily V β h)
      (latticeCell z) (β*(t^2/8)/4)) (cube L)/
      grandIntegral (gibbsFamily V β h) (cube L) ≤
        2*Real.exp (Real.exp (h+β*(t^2/2)))+(Real.exp (Real.exp (h+β*(t^2/2))))^2 := by
  have hfin : volume (cube L) ≠ ⊤ := by rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hF := cellLowerBound_gibbs_finite ht.le hβ hσ hR hs hsmall hV hVm hfin h
  have hA : 0 < t^2/8 := by positivity
  have hc : 0 ≤ β*(t^2/8)/4 := by positivity
  have hfull (i : cubeCells L) := cellLowerBound_gibbs_moment_finite ht.le hβ hσ hR hs hsmall
    hV hVm hfin h i (le_refl (β*(t^2/8)/4))
  have hhalf (i : cubeCells L) := cellLowerBound_gibbs_moment_finite ht.le hβ hσ hR hs hsmall
    hV hVm hfin h i (show (β*(t^2/8)/4)/2 ≤ β*(t^2/8)/4 by linarith only [hc])
  have hb := grand_local_moment_bound
    (gibbsFamily V β h)
    (fun i : cubeCells L => latticeCell i)
    (fun i j => physicalCoupling t σ R i j/(t^2/8))
    (measurableSet_cube L) hfin (fun i => measurableSet_latticeCell i)
    (c := β*(t^2/8)/4) (d := h+β*(t^2/2)) (v := 1)
    (gibbsFamily_relabel _ β h) (gibbsFamily_nonneg _ β h) hF hfull hhalf
    (grandIntegral_gibbs_pos _ β h (cube L) hF.summable)
    (fun i j => div_nonneg (physicalCoupling_nonneg ht.le hσ hR i j) hA.le)
    (fun i => ?_) (fun i => real_volume_cropped_cell_le_one (cube L) i) (fun i n s x hx => ?_) z
  · simpa only [one_mul] using hb
  · rw [← Finset.sum_div]
    apply (div_le_one hA).2
    have hh := (physicalCoupling_row ht.le hσ hR hs
      (fun j : cubeCells L => (j : Lattice)) Subtype.val_injective i).trans hsmall
    linarith only [hh, hA]
  · let c (j : {j : Fin n // j ∉ s}) : cubeCells L :=
      ⟨cellIndex (x j), cellIndex_mem_cubeCells (by
        have hh := hx j
        simp only [ite_eq_right j.property] at hh
        exact hh.1)⟩
    have hi := cellLowerBound_insertion_half_moments ht hβ hσ hR hs hsmall hV hVsym h x s i (by
        intro j
        have hh := hx j
        by_cases hj : j ∈ s
        · simpa only [binaryRegion, ite_eq_left hj] using hh
        · simpa only [binaryRegion, ite_eq_right hj] using hh)
      (fun j : cubeCells L => (j : Lattice)) Subtype.val_injective c (fun _ => rfl)
    convert hi using 1
    congr!

end ContinuumTemperature
end

end OAI

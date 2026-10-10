import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedWellField
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-! The actual planar counterterm field has uniform derivative bounds,
independent of the number of sites. Separated unit supports leave at most
one nonzero summand at every point. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

private theorem planarWell_derivatives_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k ≤ 6 → ∀ r : PlanarPosition,
      ‖iteratedFDeriv ℝ k manufacturedPlanarWell r‖ ≤ C := by
  have hb (k : Fin 7) : ∃ C : ℝ, ∀ r : PlanarPosition,
      ‖iteratedFDeriv ℝ k.val manufacturedPlanarWell r‖ ≤ C :=
    (manufacturedPlanarWell_C7.continuous_iteratedFDeriv (by exact_mod_cast k.isLt.le)).bounded_above_of_compact_support
      (manufacturedPlanarWell_hasCompactSupport.iteratedFDeriv k.val)
  choose B hB using hb
  let C : ℝ := 1+∑ k : Fin 7, max (B k) 0
  have hn : 0 ≤ ∑ k : Fin 7, max (B k) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro k hk r
  let j : Fin 7 := ⟨k, by omega⟩
  have hs : max (B j) 0 ≤ ∑ k : Fin 7, max (B k) 0 :=
    Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
  exact (hB j r).trans ((le_max_left _ _).trans (by dsimp [C]; linarith))

def planarWellDerivativeConstant : ℝ := Classical.choose planarWell_derivatives_bounded

theorem planarWellDerivativeConstant_positive : 0 < planarWellDerivativeConstant :=
  (Classical.choose_spec planarWell_derivatives_bounded).1

theorem planarWellDerivativeConstant_bound {k : ℕ} (hk : k ≤ 6) (r : PlanarPosition) :
    ‖iteratedFDeriv ℝ k manufacturedPlanarWell r‖ ≤ planarWellDerivativeConstant :=
  (Classical.choose_spec planarWell_derivatives_bounded).2 k hk r

private theorem well_derivative_near {k : ℕ} {r : PlanarPosition}
    (hr : iteratedFDeriv ℝ k manufacturedPlanarWell r ≠ 0) : ‖r‖ ≤ 1 := by
  have hs := (support_iteratedFDeriv_subset (𝕜 := ℝ) (f := manufacturedPlanarWell) k) hr
  have hb := (manufacturedPlanarWell_support.trans planarForcing_support) hs
  simpa only [Metric.mem_closedBall, dist_zero_right] using hb

private theorem countertermWellSum_derivative (freq scale : ℝ) {m : ℕ}
    (u : Fin m → PlanarPosition) {k : ℕ} (hk : k ≤ 6) (r : PlanarPosition) :
    iteratedFDeriv ℝ k (countertermWellSum freq scale u) r =
      ∑ i, (1+localizedCounterterm freq u i/scale) •
        iteratedFDeriv ℝ k manufacturedPlanarWell (r-u i) := by
  have hw : ContDiff ℝ k manufacturedPlanarWell :=
    manufacturedPlanarWell_C7.of_le (by exact_mod_cast (show k ≤ 7 by omega))
  unfold countertermWellSum
  rw [iteratedFDeriv_fun_sum_apply
    (f := fun i x => (1+localizedCounterterm freq u i/scale)*manufacturedPlanarWell (x-u i))
    (fun i _ => (contDiff_const.mul (hw.comp (contDiff_id.sub contDiff_const))).contDiffAt)]
  apply Finset.sum_congr rfl
  intro i _
  change iteratedFDeriv ℝ k (fun x => (1+localizedCounterterm freq u i/scale) •
    manufacturedPlanarWell (x-u i)) r = _
  rw [iteratedFDeriv_const_smul_apply' (f := fun x => manufacturedPlanarWell (x-u i))
    (a := 1+localizedCounterterm freq u i/scale)
    (hw.comp (contDiff_id.sub contDiff_const)).contDiffAt,
    iteratedFDeriv_comp_sub]

/-- Uniformity in the number of separated sites is essential for the
polynomial-time transport/cubature constants. -/
theorem countertermWellSum_derivative_bound (freq : ℝ) {scale : ℝ} (hscale : 0 < scale)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖u i-u j‖)
    (hcounter : ∀ i, localizedCounterterm freq u i ≤ scale)
    {k : ℕ} (hk : k ≤ 6) (r : PlanarPosition) :
    ‖iteratedFDeriv ℝ k (countertermWellSum freq scale u) r‖ ≤
      2*planarWellDerivativeConstant := by
  rw [countertermWellSum_derivative freq scale u hk r]
  have hcoef (i : Fin m) : |1+localizedCounterterm freq u i/scale| ≤ 2 := by
    have hlo := div_nonneg (localizedCounterterm_nonnegative freq u i) hscale.le
    have hhi := (div_le_one hscale).mpr (hcounter i)
    rw [abs_of_nonneg (by linarith)]
    linarith
  by_cases h : ∃ i, iteratedFDeriv ℝ k manufacturedPlanarWell (r-u i) ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hzero (j : Fin m) (hji : j ≠ i) :
        iteratedFDeriv ℝ k manufacturedPlanarWell (r-u j) = 0 := by
      by_contra hj
      have hri := well_derivative_near hi
      have hrj := well_derivative_near hj
      have ht : ‖u i-u j‖ ≤ ‖r-u i‖+‖r-u j‖ := by
        calc
          _ = ‖(u i-r)+(r-u j)‖ := by congr 1; abel
          _ ≤ ‖u i-r‖+‖r-u j‖ := norm_add_le _ _
          _ = _ := by rw [norm_sub_rev (u i) r]
      have hd := hsep i j hji.symm
      linarith
    rw [Finset.sum_eq_single i (fun j _ hji => by rw [hzero j hji, smul_zero])
      (fun hn => (hn (Finset.mem_univ i)).elim), norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hcoef i) (planarWellDerivativeConstant_bound hk _) (norm_nonneg _)
      (by norm_num)
  · have hzero (i : Fin m) : iteratedFDeriv ℝ k manufacturedPlanarWell (r-u i) = 0 := by
      by_contra hi
      exact h ⟨i, hi⟩
    simp only [hzero, smul_zero, Finset.sum_const_zero, norm_zero]
    exact mul_nonneg (by norm_num) planarWellDerivativeConstant_positive.le

end ContinuumCoulomb

end

end OAI

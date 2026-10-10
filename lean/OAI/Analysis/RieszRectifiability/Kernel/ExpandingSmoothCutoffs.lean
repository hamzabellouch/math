import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Expanding smooth cutoffs

Dilating a fixed bump gives compactly supported smooth cutoffs equal to one on
balls of increasing radius. Composition with linear contractions bounds all
derivatives by Schwartz seminorms and supplies uniform derivative bounds for
the cutoff errors.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff

def unitSmoothCutoff (d : ℕ) : ContDiffBump (0 : Ambient d) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def expandingSmoothCutoff (d j : ℕ) (x : Ambient d) : ℝ :=
  unitSmoothCutoff d (((j : ℝ) + 1)⁻¹ • x)

theorem expandingSmoothCutoff_smooth (d j : ℕ) :
    ContDiff ℝ ∞ (expandingSmoothCutoff d j) := by
  apply (unitSmoothCutoff d).contDiff.comp
  exact (contDiff_id : ContDiff ℝ ∞ (fun x : Ambient d => x)).const_smul _

theorem expandingSmoothCutoff_compact (d j : ℕ) :
    HasCompactSupport (expandingSmoothCutoff d j) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Ambient d) (2 * ((j : ℝ) + 1)))
  intro x hx
  apply (unitSmoothCutoff d).zero_of_le_dist
  have hR : 0 < (j : ℝ) + 1 := by positivity
  have hx' : 2 * ((j : ℝ) + 1) < ‖x‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using! hx
  change 2 ≤ dist (((j : ℝ) + 1)⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  exact (le_div_iff₀ hR).2 hx'.le |>.trans_eq (div_eq_inv_mul _ _)

theorem expandingSmoothCutoff_one (d j : ℕ) (x : Ambient d)
    (hx : x ∈ ball (0 : Ambient d) ((j : ℝ) + 1)) :
    expandingSmoothCutoff d j x = 1 := by
  apply (unitSmoothCutoff d).one_of_mem_closedBall
  have hR : 0 < (j : ℝ) + 1 := by positivity
  have hx' : ‖x‖ < (j : ℝ) + 1 := by
    simpa only [mem_ball, dist_zero_right] using! hx
  change dist (((j : ℝ) + 1)⁻¹ • x) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  have hh : ‖x‖ / ((j : ℝ) + 1) ≤ 1 := (div_le_one hR).2 hx'.le
  simpa only [div_eq_inv_mul] using! hh

theorem schwartz_contraction_derivative_bound {d : ℕ} (g : 𝓢(Ambient d, ℝ))
    (S : Ambient d →L[ℝ] Ambient d) (hS : ‖S‖ ≤ 1) (n : ℕ) (x : Ambient d) :
    ‖iteratedFDeriv ℝ n (g ∘ S) x‖ ≤ SchwartzMap.seminorm ℝ 0 n g := by
  rw [S.iteratedFDeriv_comp_right (g.smooth n) x le_rfl]
  have hp : (∏ _ : Fin n, ‖S‖) ≤ 1 := by
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hS)
  calc
    _ ≤ ‖iteratedFDeriv ℝ n g (S x)‖ * ∏ _ : Fin n, ‖S‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n g (S x)‖ := by nlinarith [norm_nonneg (iteratedFDeriv ℝ n g (S x))]
    _ ≤ _ := g.norm_iteratedFDeriv_le_seminorm ℝ n (S x)

theorem expandingSmoothCutoff_error_uniform_derivatives (d : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ j n x,
      ‖iteratedFDeriv ℝ n (fun y => expandingSmoothCutoff d j y - 1) x‖ ≤ C n := by
  let β : 𝓢(Ambient d, ℝ) := (unitSmoothCutoff d).hasCompactSupport.toSchwartzMap
    (unitSmoothCutoff d).contDiff
  refine ⟨fun n => SchwartzMap.seminorm ℝ 0 n β + 1, fun n => by positivity, ?_⟩
  intro j n x
  let S : Ambient d →L[ℝ] Ambient d := ((j : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (Ambient d)
  have hR : 1 ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hS : ‖S‖ ≤ 1 := by
    calc
      ‖S‖ ≤ ‖((j : ℝ) + 1)⁻¹‖ * ‖ContinuousLinearMap.id ℝ (Ambient d)‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ 1 * 1 := mul_le_mul
        (by rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ hR)
        ContinuousLinearMap.norm_id_le (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have heq : (expandingSmoothCutoff d j : Ambient d → ℝ) = β ∘ S := rfl
  have hb := schwartz_contraction_derivative_bound β S hS n x
  have hs : ContDiff ℝ n (expandingSmoothCutoff d j) := by
    rw [heq]
    exact (β.smooth n).comp S.contDiff
  have hc : ‖iteratedFDeriv ℝ n (fun _ : Ambient d => (1 : ℝ)) x‖ ≤ 1 := by
    cases n with
    | zero => simp
    | succ n => simp [iteratedFDeriv_succ_const]
  have hh := iteratedFDeriv_sub_apply hs.contDiffAt
    (contDiffAt_const (c := (1 : ℝ)) : ContDiffAt ℝ n (fun _ : Ambient d => (1 : ℝ)) x)
  change ‖iteratedFDeriv ℝ n ((expandingSmoothCutoff d j) - (fun _ => 1)) x‖ ≤ _
  rw [hh]
  exact (norm_sub_le _ _).trans (add_le_add (by simpa only [heq] using! hb) hc)

end

end RieszRectifiability

end OAI

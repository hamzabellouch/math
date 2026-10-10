import OAI.NumberTheory.CubicMoment.Transform.MetaplecticBilinear
import OAI.NumberTheory.CubicMoment.Estimates.SmoothShortContinuity

namespace OAI

/-! Exact Mellin separation of the actual varying outer weights in a
finite bilinear Gauss sum. All integrability follows from smooth support. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma metaplectic_mellin_term_integrable (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {V x : ℝ} (hV : 0 < V) (_hx : 0 < x) (a : ℂ) :
    Integrable (fun t : ℝ => zeroLineMellinWeight W V t*(a*mellinPhase (-t) x)) := by
  apply (zeroLineMellinWeight_integrable W hW hpos hsm hV).mul_bdd
    (c := ‖a‖)
  · have hc : Continuous (fun t : ℝ => a*mellinPhase (-t) x) := by
      unfold mellinPhase
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards with t
    simp [mellinPhase,Complex.norm_exp]

lemma metaplectic_mellin_term (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {V x : ℝ} (hV : 0 < V) (hx : 0 < x) (a : ℂ) :
    a*W (x/V) = ∫ t : ℝ, zeroLineMellinWeight W V t*(a*mellinPhase (-t) x) := by
  have h := smooth_mellin_finite (fun _ : Unit => a) (fun _ : Unit => x)
    (fun _ => hx) W hW hpos hsm 0 hV
  simp only [Fintype.sum_unique,Complex.ofReal_zero,zero_add] at h
  rw [h,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [mellinPhase_eq_cpow hx]
  have he : ((-t:ℝ):ℂ)*Complex.I = -((t:ℂ)*Complex.I) := by push_cast; ring
  rw [he]
  unfold zeroLineMellinWeight
  ring

theorem metaplectic_bilinear_mellin (A B : Finset Eisenstein)
    (α β : Eisenstein → ℂ) (W : Eisenstein → ℝ → ℂ)
    (hW : ∀ r ∈ A, HasCompactSupport (W r))
    (hpos : ∀ r ∈ A, tsupport (W r) ⊆ Set.Ioi 0)
    (hsm : ∀ r ∈ A, ContDiff ℝ ∞ (W r))
    (hB : ∀ u ∈ B, primary u) {V : ℝ} (hV : 0 < V) :
    (∑ r ∈ A, ∑ u ∈ B, α r*β u*gauss (r*u)*W r (norm u/V)) =
      ∫ t : ℝ, ∑ r ∈ A, ∑ u ∈ B,
        (α r*zeroLineMellinWeight (W r) V t)*
          (β u*mellinPhase (-t) (norm u))*gauss (r*u) := by
  let f (r u : Eisenstein) (t : ℝ) : ℂ :=
    zeroLineMellinWeight (W r) V t*((α r*β u*gauss (r*u))*mellinPhase (-t) (norm u))
  have hi (r : Eisenstein) (hr : r ∈ A) (u : Eisenstein) (hu : u ∈ B) :
      Integrable (f r u) := metaplectic_mellin_term_integrable (W r)
    (hW r hr) (hpos r hr) (hsm r hr) hV
    (norm_pos_of_ne_zero (primary_ne_zero (hB u hu))) _
  calc
    _ = ∑ r ∈ A, ∑ u ∈ B, ∫ t : ℝ, f r u t := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro u hu
      exact metaplectic_mellin_term (W r) (hW r hr) (hpos r hr) (hsm r hr) hV
        (norm_pos_of_ne_zero (primary_ne_zero (hB u hu))) _
    _ = ∫ t : ℝ, ∑ r ∈ A, ∑ u ∈ B, f r u t := by
      rw [integral_finsetSum A (fun r hr => integrable_finsetSum B (hi r hr))]
      apply Finset.sum_congr rfl
      intro r hr
      exact (integral_finsetSum B (hi r hr)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro u _
      dsimp [f]
      ring

end CubicFirstMoment

end

end OAI

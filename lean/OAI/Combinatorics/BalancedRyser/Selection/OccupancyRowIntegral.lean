import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileMeans
import OAI.Combinatorics.BalancedRyser.Selection.OccupancyVisibility

namespace OAI

namespace Balanced.OccupancyVisibility

open MeasureTheory

theorem row_summable_of_probability (p : Profile)
    (hp : HasSum p 1) (i : ℕ) : Summable (fun j : ℕ => p (i, j)) :=
  hp.summable.comp_injective (fun _ _ h => Prod.mk.inj h |>.2)

theorem row_mass_le_one (p : Profile) (hp : HasSum p 1)
    (hnonneg : ∀ ij, 0 ≤ p ij) (i : ℕ) : (∑' j : ℕ, p (i, j)) ≤ 1 := by
  simpa only [Function.comp_def, hp.tsum_eq] using
    tsum_comp_le_tsum_of_inj hp.summable hnonneg
      (i := fun j : ℕ => (i, j)) (fun _ _ h => Prod.mk.inj h |>.2)

theorem integrable_row_of_probability_support
    (ν : Measure Profile) [IsFiniteMeasure ν] (i : ℕ)
    (hsupport : ∀ᵐ x : Profile ∂ν, (∀ ij, 0 ≤ x ij) ∧ HasSum x 1) :
    Integrable (fun x : Profile => ∑' j : ℕ, x (i, j)) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    (Measurable.tsum (fun j => measurable_pi_apply (i, j))).aestronglyMeasurable
  filter_upwards [hsupport] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun j => hx.1 (i, j)))]
  exact row_mass_le_one x hx.2 hx.1 i

theorem row_integral_hasSum
    (ν : Measure Profile) [IsFiniteMeasure ν] (i : ℕ)
    (hsupport : ∀ᵐ x : Profile ∂ν, (∀ ij, 0 ≤ x ij) ∧ HasSum x 1) :
    HasSum (fun j : ℕ => ∫ x : Profile, x (i, j) ∂ν)
      (∫ x : Profile, ∑' j : ℕ, x (i, j) ∂ν) := by
  apply hasSum_integral_of_dominated_convergence (fun j (x : Profile) => x (i, j))
  · intro j
    exact (measurable_pi_apply (i, j)).aestronglyMeasurable
  · intro j
    filter_upwards [hsupport] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 (i, j))]
  · filter_upwards [hsupport] with x hx
    exact row_summable_of_probability x hx.2 i
  · exact integrable_row_of_probability_support ν i hsupport
  · filter_upwards [hsupport] with x hx
    exact (row_summable_of_probability x hx.2 i).hasSum

theorem row_integral_eq_weighted_row
    (P : Profile) (ν : Measure Profile) [IsFiniteMeasure ν]
    (hsupport : ∀ᵐ x : Profile ∂ν, (∀ ij, 0 ≤ x ij) ∧ HasSum x 1)
    (hinc : ∀ j : ℕ, (∫ x : Profile, x (0, j) ∂ν) = (j : ℝ) * P (0, j)) :
    (∫ x : Profile, ∑' j : ℕ, x (0, j) ∂ν) = ∑' j : ℕ, (j : ℝ) * P (0, j) := by
  have h := row_integral_hasSum ν 0 hsupport
  simpa only [hinc] using h.tsum_eq.symm

theorem visible_excess_of_normalized_common_sign
    (P : Profile) (νD νC : Measure Profile)
    [IsFiniteMeasure νD] [IsFiniteMeasure νC]
    {k c lam : ℝ} (hc : 0 < c) (hlam : 0 < lam)
    (hmassD : νD.real Set.univ = k) (hmassC : νC.real Set.univ = c)
    (hincD : ∀ i j : ℕ, (∫ x, x (i + 1, j) ∂νD) =
      (i + 1 : ℝ) * P (i + 1, j))
    (hincC : ∀ ij : ℕ × ℕ, (∫ x, x ij ∂νC) = (ij.2 : ℝ) * P ij)
    (hsupport : ∀ᵐ x : Profile ∂νC, (∀ ij, 0 ≤ x ij) ∧ HasSum x 1)
    (hP : HasSum (fun j : ℕ => P (0, j)) (Real.exp (-k)))
    (hdev : (∀ᵐ x : Profile ∂νC, Real.exp (-k) + lam ≤ ∑' j : ℕ, x (0, j)) ∨
      (∀ᵐ x : Profile ∂νC, (∑' j : ℕ, x (0, j)) ≤ Real.exp (-k) - lam)) :
    c < νD.real (deletionVisible P) + νC.real (coverVisible P) := by
  have hmean : HasSum (fun ij : ℕ × ℕ => (ij.2 : ℝ) * P ij) c := by
    apply deletion_profile_second_mean νC (fun ij (x : Profile) => x ij) P c
    · intro ij
      exact (measurable_pi_apply ij).aestronglyMeasurable
    · intro ij
      exact hsupport.mono (fun x hx => hx.1 ij)
    · exact hsupport.mono (fun x hx => hx.2)
    · exact hincC
    · exact hmassC
  exact visible_excess_of_common_sign P νD νC hc hlam hmassD hmassC hincD
    hmean hP (integrable_row_of_probability_support νC 0 hsupport)
    (row_integral_eq_weighted_row P νC hsupport (fun j => hincC (0, j))) hdev

end Balanced.OccupancyVisibility

end OAI

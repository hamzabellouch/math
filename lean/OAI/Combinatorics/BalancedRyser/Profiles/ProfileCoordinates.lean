import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Profiles.Profile
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileWeakLimits

namespace OAI

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Balanced
open scoped _root_.Balanced

def clippedProfileCoordinate (ij : ℕ × ℕ) : Profile →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max 0 (min 1 (x ij)))
    (continuous_const.max (continuous_const.min (continuous_apply ij))) 1
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le (by norm_num) (min_le_left _ _))

@[simp] theorem clippedProfileCoordinate_apply (ij : ℕ × ℕ) (x : Profile) :
    clippedProfileCoordinate ij x = max 0 (min 1 (x ij)) := rfl

theorem clippedProfileCoordinate_nonneg (ij : ℕ × ℕ) (x : Profile) :
    0 ≤ clippedProfileCoordinate ij x := le_max_left _ _

theorem clippedProfileCoordinate_eq {ij : ℕ × ℕ} {x : Profile}
    (hzero : 0 ≤ x ij) (hone : x ij ≤ 1) :
    clippedProfileCoordinate ij x = x ij := by
  simp only [clippedProfileCoordinate_apply, min_eq_right hone, max_eq_right hzero]

theorem boundedProfile_coordinate_bounds {M : ℝ} {x : Profile}
    (hx : IsBoundedProfile M x) (ij : ℕ × ℕ) : 0 ≤ x ij ∧ x ij ≤ 1 := by
  refine ⟨hx.1 ij, ?_⟩
  have h := hx.2.1.summable.le_tsum ij (fun j _ => hx.1 j)
  simpa only [hx.2.1.tsum_eq] using h

theorem clippedProfileCoordinate_eq_of_bounded {M : ℝ} {x : Profile}
    (hx : IsBoundedProfile M x) (ij : ℕ × ℕ) :
    clippedProfileCoordinate ij x = x ij :=
  clippedProfileCoordinate_eq (boundedProfile_coordinate_bounds hx ij).1
    (boundedProfile_coordinate_bounds hx ij).2

def profileCoordinateDeviation (ij : ℕ × ℕ) : Profile →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min 1 |x ij - clippedProfileCoordinate ij x|)
    (continuous_const.min ((continuous_apply ij).sub
      (clippedProfileCoordinate ij).continuous).abs) 1
    (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) (abs_nonneg _))]
      exact min_le_left _ _)

lemma profileCoordinateDeviation_nonneg (ij : ℕ × ℕ) (x : Profile) :
    0 ≤ profileCoordinateDeviation ij x := le_min (by norm_num) (abs_nonneg _)

lemma profileCoordinateDeviation_zero_iff (ij : ℕ × ℕ) (x : Profile) :
    profileCoordinateDeviation ij x = 0 ↔ x ij = clippedProfileCoordinate ij x := by
  change min 1 |x ij - clippedProfileCoordinate ij x| = 0 ↔ _
  constructor
  · intro hz
    by_contra hne
    have hp : 0 < min 1 |x ij - clippedProfileCoordinate ij x| :=
      lt_min (by norm_num) (abs_pos.mpr (sub_ne_zero.mpr hne))
    linarith
  · intro h
    rw [sub_eq_zero.mpr h, abs_zero]
    norm_num

theorem profile_coordinate_bounds_weak_limit
    {νn : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    (ij : ℕ × ℕ) (hν : Tendsto νn atTop (𝓝 ν))
    (hb : ∀ n, ∀ᵐ x ∂(νn n : Measure Profile), 0 ≤ x ij ∧ x ij ≤ 1) :
    ∀ᵐ x ∂(ν : Measure Profile), 0 ≤ x ij ∧ x ij ≤ 1 := by
  have hz : ∀ᵐ x ∂(ν : Measure Profile), profileCoordinateDeviation ij x = 0 := by
    apply profile_zero_coordinate_weak_limit hν (profileCoordinateDeviation ij)
      (profileCoordinateDeviation_nonneg ij)
    intro n
    filter_upwards [hb n] with x hx
    apply (profileCoordinateDeviation_zero_iff ij x).mpr
    exact (clippedProfileCoordinate_eq hx.1 hx.2).symm
  filter_upwards [hz] with x hx
  rw [(profileCoordinateDeviation_zero_iff ij x).mp hx]
  exact ⟨clippedProfileCoordinate_nonneg ij x,
    max_le (by norm_num) (min_le_left _ _)⟩

theorem ambient_profile_incidence_weak_limit
    {νn : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    {Pn : ℕ → Profile} {P : Profile} {w : ℝ} (ij : ℕ × ℕ)
    (hν : Tendsto νn atTop (𝓝 ν)) (hP : Tendsto Pn atTop (𝓝 P))
    (hb : ∀ n, ∀ᵐ x ∂(νn n : Measure Profile), 0 ≤ x ij ∧ x ij ≤ 1)
    (hinc : ∀ n, (∫ x, x ij ∂(νn n : Measure Profile)) = w * Pn n ij) :
    (∫ x, x ij ∂(ν : Measure Profile)) = w * P ij := by
  have heq (n : ℕ) : (∫ x, clippedProfileCoordinate ij x ∂(νn n : Measure Profile)) =
      ∫ x, x ij ∂(νn n : Measure Profile) := by
    apply integral_congr_ae
    filter_upwards [hb n] with x hx
    exact clippedProfileCoordinate_eq hx.1 hx.2
  have hlim : (∫ x, clippedProfileCoordinate ij x ∂(ν : Measure Profile)) =
      ∫ x, x ij ∂(ν : Measure Profile) := by
    apply integral_congr_ae
    filter_upwards [profile_coordinate_bounds_weak_limit ij hν hb] with x hx
    exact clippedProfileCoordinate_eq hx.1 hx.2
  rw [← hlim]
  apply profile_incidence_weak_limit hν (clippedProfileCoordinate ij)
    ((continuous_apply ij).tendsto P |>.comp hP)
  intro n
  rw [heq, hinc]
  rfl

theorem boundedProfile_incidence_weak_limit
    {νn : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    {Pn : ℕ → Profile} {P : Profile} {M w : ℝ} (ij : ℕ × ℕ)
    (hν : Tendsto νn atTop (𝓝 ν)) (hP : Tendsto Pn atTop (𝓝 P))
    (hsuppn : ∀ n, ∀ᵐ x ∂(νn n : Measure Profile), IsBoundedProfile M x)
    (hsupp : ∀ᵐ x ∂(ν : Measure Profile), IsBoundedProfile M x)
    (hinc : ∀ n, (∫ x, x ij ∂(νn n : Measure Profile)) = w * Pn n ij) :
    (∫ x, x ij ∂(ν : Measure Profile)) = w * P ij := by
  have hn (n : ℕ) : (∫ x, clippedProfileCoordinate ij x ∂(νn n : Measure Profile)) =
      ∫ x, x ij ∂(νn n : Measure Profile) := by
    apply integral_congr_ae
    filter_upwards [hsuppn n] with x hx
    exact clippedProfileCoordinate_eq_of_bounded hx ij
  have hlim : (∫ x, clippedProfileCoordinate ij x ∂(ν : Measure Profile)) =
      ∫ x, x ij ∂(ν : Measure Profile) := by
    apply integral_congr_ae
    filter_upwards [hsupp] with x hx
    exact clippedProfileCoordinate_eq_of_bounded hx ij
  rw [← hlim]
  apply profile_incidence_weak_limit hν (clippedProfileCoordinate ij)
    ((continuous_apply ij).tendsto P |>.comp hP)
  intro n
  rw [hn, hinc]
  rfl

theorem boundedProfile_zero_coordinate_weak_limit
    {νn : ℕ → FiniteMeasure Profile} {ν : FiniteMeasure Profile}
    {M : ℝ} (ij : ℕ × ℕ) (hν : Tendsto νn atTop (𝓝 ν))
    (hsupp : ∀ᵐ x ∂(ν : Measure Profile), IsBoundedProfile M x)
    (hzero : ∀ n, ∀ᵐ x ∂(νn n : Measure Profile), x ij = 0) :
    ∀ᵐ x ∂(ν : Measure Profile), x ij = 0 := by
  have hclip : ∀ᵐ x ∂(ν : Measure Profile), clippedProfileCoordinate ij x = 0 := by
    apply profile_zero_coordinate_weak_limit hν (clippedProfileCoordinate ij)
      (clippedProfileCoordinate_nonneg ij)
    intro n
    filter_upwards [hzero n] with x hx
    simp [hx]
  filter_upwards [hsupp, hclip] with x hx hz
  rw [clippedProfileCoordinate_eq_of_bounded hx ij] at hz
  exact hz

end Balanced

end OAI

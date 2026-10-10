import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Order.Filter.Finite

namespace OAI

/-! # The active hyperplanes of a polyhedral extreme ray

If a direction annihilates every inequality active at an extreme ray, small
positive and negative perturbations stay in the cone. Extremality therefore
forces that direction onto the ray's line. The cone inequalities choose the
nonnegative half-line.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Finite I]

def linearInequalityCone (α : I → W →L[ℝ] ℝ) : Set W := {w | ∀ i, 0 ≤ α i w}

def nonnegativeRay (w : W) : Set W := {x | ∃ r : ℝ, 0 ≤ r ∧ x = r • w}

theorem exists_two_sided_cone_perturbation (α : I → W →L[ℝ] ℝ)
    {w x : W} (hw : w ∈ linearInequalityCone α)
    (hx : ∀ i, α i w = 0 → α i x = 0) :
    ∃ t : ℝ, 0 < t ∧ w + t • x ∈ linearInequalityCone α ∧
      w - t • x ∈ linearInequalityCone α := by
  have hevent (i : I) : ∀ᶠ t : ℝ in 𝓝 0,
      0 ≤ α i (w + t • x) ∧ 0 ≤ α i (w - t • x) := by
    by_cases hi : α i w = 0
    · exact Eventually.of_forall (fun t => by simp only [map_add, map_sub, map_smul,
        hi, hx i hi, smul_eq_mul, mul_zero, add_zero, sub_zero, le_refl, and_self])
    · have hp : 0 < α i w := lt_of_le_of_ne (hw i) (Ne.symm hi)
      have hp' : 0 < α i (w + (0 : ℝ) • x) := by simpa using hp
      have hm' : 0 < α i (w - (0 : ℝ) • x) := by simpa using hp
      have hplus : Continuous (fun t : ℝ => α i (w + t • x)) := by fun_prop
      have hminus : Continuous (fun t : ℝ => α i (w - t • x)) := by fun_prop
      filter_upwards [(isOpen_lt continuous_const hplus).mem_nhds hp',
        (isOpen_lt continuous_const hminus).mem_nhds hm'] with t ht hu
      exact ⟨ht.le, hu.le⟩
  have hall := eventually_all.mpr hevent
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hall
  have hsmall : dist (ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact ⟨ε / 2, by positivity, fun i => (he hsmall i).1, fun i => (he hsmall i).2⟩

/-- This uses the standard `IsExtreme` predicate on the actual nonnegative
ray, rather than assuming a description of the active hyperplanes. -/
theorem eq_smul_of_active_constraints (α : I → W →L[ℝ] ℝ) {w x : W}
    (hExt : IsExtreme ℝ (linearInequalityCone α) (nonnegativeRay w))
    (hx : ∀ i, α i w = 0 → α i x = 0) : ∃ r : ℝ, x = r • w := by
  have hw : w ∈ linearInequalityCone α := hExt.subset ⟨1, zero_le_one, by simp⟩
  obtain ⟨t, ht, hp, hm⟩ := exists_two_sided_cone_perturbation α hw hx
  have hmid : w ∈ openSegment ℝ (w + t • x) (w - t • x) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    rw [smul_add, smul_sub]
    calc
      (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • (t • x) +
          ((1 / 2 : ℝ) • w - (1 / 2 : ℝ) • (t • x)) =
          (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • w := by abel
      _ = w := by rw [← add_smul]; norm_num
  obtain ⟨r, _hr, he⟩ := hExt.left_mem_of_mem_openSegment hp hm
    (show w ∈ nonnegativeRay w from ⟨1, zero_le_one, by simp⟩) hmid
  have htx : t • x = (r - 1) • w := by
    calc
      t • x = (w + t • x) - w := by abel
      _ = r • w - (1 : ℝ) • w := by rw [he, one_smul]
      _ = (r - 1) • w := (sub_smul r 1 w).symm
  refine ⟨t⁻¹ * (r - 1), ?_⟩
  calc
    x = t⁻¹ • (t • x) := by rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    _ = (t⁻¹ * (r - 1)) • w := by rw [htx, smul_smul]

theorem mem_ray_of_active_constraints (α : I → W →L[ℝ] ℝ)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0) {w x : W}
    (hExt : IsExtreme ℝ (linearInequalityCone α) (nonnegativeRay w))
    (hxcone : x ∈ linearInequalityCone α)
    (hx : ∀ i, α i w = 0 → α i x = 0) : x ∈ nonnegativeRay w := by
  obtain ⟨r, rfl⟩ := eq_smul_of_active_constraints α hExt hx
  by_cases hw : w = 0
  · exact ⟨0, le_rfl, by simp [hw]⟩
  have hwcone : w ∈ linearInequalityCone α := hExt.subset ⟨1, zero_le_one, by simp⟩
  have hi : ∃ i, 0 < α i w := by
    by_contra! hn
    apply hw
    apply hsep
    intro i
    exact le_antisymm (hn i) (hwcone i)
  obtain ⟨i, hi⟩ := hi
  have hri := hxcone i
  simp only [map_smul, smul_eq_mul] at hri
  exact ⟨r, by nlinarith, rfl⟩

theorem eq_of_mem_nonnegativeRay_of_norm_eq {x y : W}
    (hy : y ∈ nonnegativeRay x) (hnorm : ‖y‖ = ‖x‖) : y = x := by
  obtain ⟨r, hr, rfl⟩ := hy
  by_cases hx : x = 0
  · simp [hx]
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr] at hnorm
    have h1 : r = 1 := by nlinarith
    rw [h1, one_smul]

end PolycyclicRecognition

end

end OAI

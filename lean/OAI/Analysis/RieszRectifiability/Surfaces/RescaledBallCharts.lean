import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
A Lipschitz chart on a centered ball can be translated and rescaled without changing its image.
Rescaling the parameter ball by the inverse factor multiplies the Lipschitz bound by that factor.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set
open scoped NNReal

theorem exists_rescaled_ball_chart {n d : ℕ}
    (r : ℝ) (a : Ambient n) (s : ℝ≥0) (hs : 0 < s)
    (f : ball (0 : Ambient n) r → Ambient d) (M : ℝ≥0) (hf : LipschitzWith M f) :
    ∃ g : Ambient n → Ambient d,
      LipschitzOnWith (M * s) g (ball a (r / (s : ℝ))) ∧
      g '' ball a (r / (s : ℝ)) = Set.range f := by
  classical
  have hsr : 0 < (s : ℝ) := hs
  have hnorm (u : Ambient n) : ‖(s : ℝ) • (u - a)‖ = (s : ℝ) * dist u a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg, dist_eq_norm]
  have hmem (u : Ambient n) (hu : u ∈ ball a (r / (s : ℝ))) :
      (s : ℝ) • (u - a) ∈ ball (0 : Ambient n) r := by
    rw [mem_ball_zero_iff]
    rw [hnorm]
    have h := (lt_div_iff₀ hsr).mp hu
    simpa only [mul_comm] using! h
  let T : ball a (r / (s : ℝ)) → ball (0 : Ambient n) r :=
    fun u => ⟨(s : ℝ) • (u.val - a), hmem u.val u.property⟩
  have hTdist (u v : ball a (r / (s : ℝ))) :
      dist (T u) (T v) = (s : ℝ) * dist u v := by
    change dist ((s : ℝ) • (u.val - a)) ((s : ℝ) • (v.val - a)) =
      (s : ℝ) * dist u.val v.val
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg s.coe_nonneg]
    congr 1
    simp only [dist_eq_norm]
    congr 1
    abel
  have hsurj : Function.Surjective T := by
    intro v
    let u : Ambient n := a + (s : ℝ)⁻¹ • v.val
    have hu : u ∈ ball a (r / (s : ℝ)) := by
      change dist (a + (s : ℝ)⁻¹ • v.val) a < r / (s : ℝ)
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hsr)]
      have hv : ‖v.val‖ < r := mem_ball_zero_iff.mp v.property
      have h := mul_lt_mul_of_pos_left hv (inv_pos.mpr hsr)
      simpa only [div_eq_mul_inv, mul_comm] using! h
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    change (s : ℝ) • ((a + (s : ℝ)⁻¹ • v.val) - a) = v.val
    rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hsr.ne', one_smul]
  let g : Ambient n → Ambient d := fun u =>
    if hu : u ∈ ball a (r / (s : ℝ)) then f (T ⟨u, hu⟩) else 0
  have hg (u : Ambient n) (hu : u ∈ ball a (r / (s : ℝ))) : g u = f (T ⟨u, hu⟩) := by
    simp only [g, dite_eq_left hu]
  refine ⟨g, ?_, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    rw [hg u hu, hg v hv]
    have h := hf.dist_le_mul (T ⟨u, hu⟩) (T ⟨v, hv⟩)
    rw [hTdist] at h
    simpa only [NNReal.coe_mul, Subtype.dist_eq, mul_assoc] using! h
  · apply Set.Subset.antisymm
    · rintro y ⟨u, hu, rfl⟩
      exact ⟨T ⟨u, hu⟩, (hg u hu).symm⟩
    · rintro y ⟨v, rfl⟩
      obtain ⟨u, hu⟩ := hsurj v
      exact ⟨u.val, u.property, (hg u.val u.property).trans (congrArg f hu)⟩

end

end RieszRectifiability

end OAI

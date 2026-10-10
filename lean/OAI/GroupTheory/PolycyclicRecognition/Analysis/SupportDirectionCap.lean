import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

namespace OAI

/-! # Separating one unsupported direction by a small cap

The cap preserves all the supports in a finite list of directions and
strictly lowers support in a direction outside their positive rays.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I]

/-- A compact convex truncation of the unit ball leaves the prescribed
support values unchanged but strictly lowers support in any additional
direction not on their positive rays. -/
theorem exists_support_direction_cap (v : I → W) (b : W) (hb : b ≠ 0)
    (hnot : ∀ i (r : ℝ), 0 < r → b ≠ r • v i) :
    ∃ E : Set W, IsCompact E ∧ E.Nonempty ∧ Convex ℝ E ∧
      E ⊆ Metric.closedBall 0 1 ∧
      (∀ i, ∃ x ∈ E, inner ℝ (v i) x = ‖v i‖) ∧
      ∃ c : ℝ, c < ‖b‖ ∧ ∀ x ∈ E, inner ℝ b x ≤ c := by
  classical
  let u : I → W := fun i => ‖v i‖⁻¹ • v i
  have hunorm (i : I) : ‖u i‖ ≤ 1 := by
    by_cases hv : v i = 0
    · simp [u, hv]
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp [u, norm_smul, hvn]
  have huinner (i : I) : inner ℝ (v i) (u i) = ‖v i‖ := by
    by_cases hv : v i = 0
    · simp [u, hv]
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      simp only [u, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
  have hult (i : I) : inner ℝ b (u i) < ‖b‖ := by
    by_cases hv : v i = 0
    · simpa [u, hv] using norm_pos_iff.mpr hb
    · have hvn : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hunit : ‖u i‖ = 1 := by
        simp [u, norm_smul, hvn]
      have hne : ‖u i‖ • b ≠ ‖b‖ • u i := by
        intro heq
        have heq' : b = (‖b‖ / ‖v i‖) • v i := by
          simpa only [hunit, one_smul, u, smul_smul, div_eq_mul_inv] using heq
        exact hnot i (‖b‖ / ‖v i‖)
          (div_pos (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hv)) heq'
      simpa only [hunit, mul_one] using (inner_lt_norm_mul_iff_real.mpr hne)
  let x : Option I → W := fun i => i.elim 0 u
  let c : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i : Option I => inner ℝ b (x i))
  have hc0 : 0 ≤ c := by
    have hh := Finset.le_sup' (f := fun i : Option I => inner ℝ b (x i))
      (Finset.mem_univ none)
    simpa only [x, Option.elim_none, inner_zero_right] using hh
  have hcb : c < ‖b‖ := by
    rw [Finset.sup'_lt_iff]
    intro i _
    cases i with
    | none => simpa only [x, Option.elim_none, inner_zero_right] using norm_pos_iff.mpr hb
    | some i => exact hult i
  let E := Metric.closedBall (0 : W) 1 ∩ {y : W | inner ℝ b y ≤ c}
  have hclosed : IsClosed {y : W | inner ℝ b y ≤ c} :=
    isClosed_le (continuous_const.inner continuous_id) continuous_const
  have hcompact : IsCompact E := (isCompact_closedBall (0 : W) 1).inter_right hclosed
  have hconvex : Convex ℝ E := (convex_closedBall (0 : W) 1).inter
    (convex_halfSpace_le (innerSL ℝ b).toLinearMap.isLinear c)
  refine ⟨E, hcompact, ⟨0, ?_⟩, hconvex, inter_subset_left, ?_, c, hcb, ?_⟩
  · exact ⟨by simp, by simpa using hc0⟩
  · intro i
    refine ⟨u i, ⟨?_, ?_⟩, huinner i⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hunorm i
    · exact Finset.le_sup' (f := fun j : Option I => inner ℝ b (x j))
        (Finset.mem_univ (some i))
  · exact fun _ hy => hy.2

end PolycyclicRecognition

end

end OAI

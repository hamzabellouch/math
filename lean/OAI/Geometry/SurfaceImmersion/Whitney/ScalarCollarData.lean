import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs
import OAI.Geometry.SurfaceImmersion.Geometry.BlendedDensityCompact

namespace OAI

/-! Construct the scalar angle data from a local calibrated collar and an
interior target in the open unit disk. The cutoffs are actual smooth functions. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem scalar_collar_data {C L U : Set E} (hC : IsCompact C)
    (hU : IsOpen U) (hCU : C ⊆ U)
    {β : E → ℝ} {c : E → LoopDensity.Plane}
    (hβ : ContDiffOn ℝ ∞ β U)
    (hβpos : ∀ x ∈ (L \ C) ∩ U, 0 < β x)
    (hcal : ∀ x ∈ U, c x = ![(1 - β x ^ 2 / 2) / (1 + β x ^ 2 / 2), 0])
    (hinterior : ∀ x ∈ L \ C, c x 0 ^ 2 + c x 1 ^ 2 < 1) :
    ∃ W : Set E, IsOpen W ∧ C ⊆ W ∧ W ⊆ U ∧
      ∃ b s : E → ℝ, ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ s ∧
        (∀ x, s x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x ∈ L \ W, 0 < b x) ∧
        (∀ x ∈ W, b x = β x ∧ s x = 0 ∧
          c x = ![(1 - b x ^ 2 / 2) / (1 + b x ^ 2 / 2), 0]) ∧
        (∀ x ∈ L \ W,
          (0 < b x ∧ 2 * Real.arctan (b x) ≤ Real.pi + 1 ∧
            s x ∈ Icc (0 : ℝ) 1 ∧
            c x = ![(1 - b x ^ 2 / 2) / (1 + b x ^ 2 / 2), 0]) ∨
          (s x = 1 ∧ Real.pi < Real.pi + 1 ∧ c x 0 ^ 2 + c x 1 ^ 2 < 1)) := by
  obtain ⟨W, hW, hCW, hWU, φ, χ, hφ, hχ, _, _, hφr, hχr,
    hχs, hφs, hφone, hχone⟩ := nested_compact_cutoffs hC hU hCU
  let b : E → ℝ := fun x => χ x * β x + (1 - χ x)
  let s : E → ℝ := fun x => 1 - φ x
  have hb : ContDiff ℝ ∞ b :=
    (supported_local_mul hU hχ hβ hχs).add (contDiff_const.sub hχ)
  have hs : ContDiff ℝ ∞ s := contDiff_const.sub hφ
  have hsr (x : E) : s x ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨hl, hu⟩ := hφr x
    exact ⟨by dsimp [s]; linarith, by dsimp [s]; linarith⟩
  have hnc (x : E) (hx : x ∈ L \ W) : x ∈ L \ C :=
    ⟨hx.1, fun hc => hx.2 (hCW hc)⟩
  have hbp (x : E) (hx : x ∈ L \ W) : 0 < b x := by
    obtain ⟨hl, hu⟩ := hχr x
    by_cases hz : χ x = 0
    · simp [b, hz]
    · have hxp : x ∈ U := hχs (subset_tsupport χ (Function.mem_support.mpr hz))
      have hp := hβpos x ⟨hnc x hx, hxp⟩
      have hχp : 0 < χ x := lt_of_le_of_ne hl (Ne.symm hz)
      dsimp [b]
      exact add_pos_of_pos_of_nonneg (mul_pos hχp hp) (sub_nonneg.mpr hu)
  have hwb (x : E) (hx : x ∈ W) : b x = β x := by
    have hφnz : φ x ≠ 0 := by rw [hφone x hx]; norm_num
    have hχx := hχone x (subset_tsupport φ (Function.mem_support.mpr hφnz))
    simp [b, hχx]
  refine ⟨W, hW, hCW, hWU, b, s, hb, hs, hsr, hbp, ?_, ?_⟩
  · intro x hx
    exact ⟨hwb x hx, by simp [s, hφone x hx], by rw [hwb x hx]; exact hcal x (hWU hx)⟩
  · intro x hx
    by_cases hfull : s x = 1
    · exact Or.inr ⟨hfull, by linarith, hinterior x (hnc x hx)⟩
    · have hφnz : φ x ≠ 0 := by intro hz; exact hfull (by simp [s, hz])
      have hxs := subset_tsupport φ (Function.mem_support.mpr hφnz)
      have hbx : b x = β x := by simp [b, hχone x hxs]
      refine Or.inl ⟨hbp x hx, ?_, hsr x, ?_⟩
      · linarith [Real.arctan_lt_pi_div_two (b x)]
      · rw [hbx]
        exact hcal x (hφs hxs)

end ClosedSurfaceR4.CollarVelocity

end

end OAI

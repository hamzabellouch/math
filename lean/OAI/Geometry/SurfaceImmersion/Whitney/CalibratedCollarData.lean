import OAI.Geometry.SurfaceImmersion.Whitney.ScalarCollarData
import OAI.Geometry.SurfaceImmersion.Whitney.CollarVelocityCalibration

namespace OAI

/-! Obtain the scalar loop data from smooth radius and velocity coordinates,
including the extension from the admissible parameter neighborhood. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity

lemma calibrated_rational_mean {R v a : ℝ} (hR : 0 < R) (hv : 0 < v)
    (hquad : R ^ 2 = v ^ 2 + a ^ 2) :
    (1 - amplitude R v a ^ 2 / 2) / (1 + amplitude R v a ^ 2 / 2) = v / R := by
  rw [← mean_density_arcX]
  exact calibrated_mean hR hv hquad

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem calibrated_collar_data {C L U Ω : Set E}
    (hC : IsCompact C) (hL : IsCompact L) (hCL : C ⊆ L)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
    {R u v a : E → ℝ} (hR : ContDiffOn ℝ ∞ R Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) (hv : ContDiffOn ℝ ∞ v Ω)
    (ha : ContDiffOn ℝ ∞ a Ω)
    (hRp : ∀ x ∈ Ω, 0 < R x)
    (hquad : ∀ x ∈ Ω, R x ^ 2 = u x ^ 2 + v x ^ 2 + a x ^ 2)
    (hup : ∀ x ∈ U, 0 < u x) (hvz : ∀ x ∈ U, v x = 0)
    (hap : ∀ x ∈ L \ C, 0 < a x) :
    ∃ c : E → LoopDensity.Plane, ContDiff ℝ ∞ c ∧
      ∃ V : Set E, IsOpen V ∧ L ⊆ V ∧ V ⊆ Ω ∧
      (∀ x ∈ V, c x = ![u x / R x, v x / R x]) ∧
      ∃ W : Set E, IsOpen W ∧ C ⊆ W ∧ W ⊆ U ∧
        ∃ b s : E → ℝ, ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ s ∧
          (∀ x, s x ∈ Icc (0 : ℝ) 1) ∧
          (∀ x ∈ L \ W, 0 < b x) ∧
          (∀ x ∈ W, b x = amplitude (R x) (u x) (a x) ∧ s x = 0 ∧
            c x = ![(1 - b x ^ 2 / 2) / (1 + b x ^ 2 / 2), 0]) ∧
          (∀ x ∈ L \ W,
            (0 < b x ∧ 2 * Real.arctan (b x) ≤ Real.pi + 1 ∧
              s x ∈ Icc (0 : ℝ) 1 ∧
              c x = ![(1 - b x ^ 2 / 2) / (1 + b x ^ 2 / 2), 0]) ∨
            (s x = 1 ∧ Real.pi < Real.pi + 1 ∧ c x 0 ^ 2 + c x 1 ^ 2 < 1)) := by
  let target : E → LoopDensity.Plane := fun x => ![u x / R x, v x / R x]
  have htarget : ContDiffOn ℝ ∞ target Ω := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact hu.div hR (fun x hx => (hRp x hx).ne')
    · exact hv.div hR (fun x hx => (hRp x hx).ne')
  obtain ⟨V, hV, hLV, hVΩ, c, hc, hct⟩ := compact_smooth_extension hL hΩ hLΩ htarget
  let U' := U ∩ V
  have hU' : IsOpen U' := hU.inter hV
  have hCU' : C ⊆ U' := fun x hx => ⟨hCU hx, hLV (hCL hx)⟩
  have hβ : ContDiffOn ℝ ∞ (fun x => amplitude (R x) (u x) (a x)) U' := by
    exact (contDiffOn_const.mul (ha.mono (inter_subset_left.trans hUΩ))).div
      ((hR.add hu).mono (inter_subset_left.trans hUΩ))
      (fun x hx => (add_pos (hRp x (hUΩ hx.1)) (hup x hx.1)).ne')
  have hβp : ∀ x ∈ (L \ C) ∩ U', 0 < amplitude (R x) (u x) (a x) := by
    intro x hx
    exact div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (hap x hx.1))
      (add_pos (hRp x (hUΩ hx.2.1)) (hup x hx.2.1))
  have hcal : ∀ x ∈ U', c x =
      ![(1 - amplitude (R x) (u x) (a x) ^ 2 / 2) /
        (1 + amplitude (R x) (u x) (a x) ^ 2 / 2), 0] := by
    intro x hx
    rw [hct hx.2]
    have hq : R x ^ 2 = u x ^ 2 + a x ^ 2 := by
      simpa [hvz x hx.1] using hquad x (hUΩ hx.1)
    rw [calibrated_rational_mean (hRp x (hUΩ hx.1)) (hup x hx.1) hq]
    simp [target, hvz x hx.1]
  have hi : ∀ x ∈ L \ C, c x 0 ^ 2 + c x 1 ^ 2 < 1 := by
    intro x hx
    rw [hct (hLV hx.1)]
    change (u x / R x) ^ 2 + (v x / R x) ^ 2 < 1
    have hr := hRp x (hLΩ hx.1)
    have hq := hquad x (hLΩ hx.1)
    have ha' := hap x hx
    rw [div_pow, div_pow, ← add_div, div_lt_one (sq_pos_of_pos hr)]
    nlinarith [sq_pos_of_pos ha']
  obtain ⟨W, hW, hCW, hWU', b, s, hb, hs, hsr, hbp, hw, hshape⟩ :=
    scalar_collar_data hC hU' hCU' hβ hβp hcal hi
  exact ⟨c, hc, V, hV, hLV, hVΩ, hct, W, hW, hCW,
    hWU'.trans inter_subset_left, b, s, hb, hs, hsr, hbp, hw, hshape⟩

end ClosedSurfaceR4.CollarVelocity

end

end OAI

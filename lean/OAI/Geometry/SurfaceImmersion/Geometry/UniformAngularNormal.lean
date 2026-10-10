import OAI.Geometry.SurfaceImmersion.Primitive.VelocitySpatialBounds

namespace OAI

/-! Normal length bounds over every angle, fixed before the turn translation
or any of its derivatives is chosen. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem uniform_angular_normal_bounds {X Y C e₁ e₂ : E → Vec} {R : E → ℝ} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) (hC : ContDiffOn ℝ ∞ C U)
    (h₁ : ContDiffOn ℝ ∞ e₁ U) (h₂ : ContDiffOn ℝ ∞ e₂ U) (hR : ContDiffOn ℝ ∞ R U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (he₁ : ∀ x ∈ U, e₁ x ⬝ᵥ e₁ x = 1) (he₂ : ∀ x ∈ U, e₂ x ⬝ᵥ e₂ x = 1)
    (he₁₂ : ∀ x ∈ U, e₁ x ⬝ᵥ e₂ x = 0)
    (hYe₁ : ∀ x ∈ U, Y x ⬝ᵥ e₁ x = 0) (hYe₂ : ∀ x ∈ U, Y x ⬝ᵥ e₂ x = 0)
    (hCe₁ : ∀ x ∈ U, C x ⬝ᵥ e₁ x = 0) (hCe₂ : ∀ x ∈ U, C x ⬝ᵥ e₂ x = 0)
    (hR0 : ∀ x ∈ U, R x ≠ 0) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ x ∈ K, ∀ α : ℝ,
      c ≤ normalSize (X x) (Y x) (C x) (R x • direction (e₁ x) (e₂ x) α) ∧
      normalSize (X x) (Y x) (C x) (R x • direction (e₁ x) (e₂ x) α) ≤ D ∧
      1 / normalSize (X x) (Y x) (C x) (R x • direction (e₁ x) (e₂ x) α) ≤ 1 / c := by
  let V : E × ℝ → Vec := fun z => R z.1 • direction (e₁ z.1) (e₂ z.1) z.2
  have hV : ContDiffOn ℝ ∞ V (U ×ˢ univ) :=
    (hR.comp contDiffOn_fst (fun z hz => hz.1)).smul
      ((contDiffOn_snd.cos.smul (h₁.comp contDiffOn_fst (fun z hz => hz.1))).add
        (contDiffOn_snd.sin.smul (h₂.comp contDiffOn_fst (fun z hz => hz.1))))
  have hYV (z : E × ℝ) (hz : z ∈ U ×ˢ (univ : Set ℝ)) : Y z.1 ⬝ᵥ V z = 0 := by
    simp only [V, direction, dotProduct_smul, dotProduct_add, hYe₁ z.1 hz.1,
      hYe₂ z.1 hz.1, smul_zero, add_zero]
  have hCV (z : E × ℝ) (hz : z ∈ U ×ˢ (univ : Set ℝ)) : C z.1 ⬝ᵥ V z = 0 := by
    simp only [V, direction, dotProduct_smul, dotProduct_add, hCe₁ z.1 hz.1,
      hCe₂ z.1 hz.1, smul_zero, add_zero]
  have hV0 (z : E × ℝ) (hz : z ∈ U ×ˢ (univ : Set ℝ)) : V z ≠ 0 := by
    apply smul_ne_zero (hR0 z.1 hz.1)
    intro hh
    have hu := direction_unit (he₁ z.1 hz.1) (he₂ z.1 hz.1) (he₁₂ z.1 hz.1) z.2
    rw [hh] at hu
    simp at hu
  have hp : 0 < 2 * Real.pi := by positivity
  obtain ⟨c, D, hc, hDD, hb⟩ := compact_normalSize_bounds
    (hU.prod isOpen_univ) (hX.comp contDiffOn_fst (fun z hz => hz.1))
    (hY.comp contDiffOn_fst (fun z hz => hz.1))
    (hC.comp contDiffOn_fst (fun z hz => hz.1)) hV
    (fun z hz => hD z.1 hz.1) hYV hCV hV0
    (hK.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi))))
    (prod_mono hKU (subset_univ _))
  refine ⟨c, D, hc, hDD, ?_⟩
  intro x hx α
  let β := toIcoMod hp 0 α
  have hβ : β ∈ Icc (0 : ℝ) (2 * Real.pi) := by
    have hm := toIcoMod_mem_Ico hp 0 α
    exact ⟨hm.1, by simpa only [zero_add] using hm.2.le⟩
  have hcos : Real.cos β = Real.cos α :=
    Real.cos_periodic.sub_zsmul_eq (toIcoDiv hp 0 α)
  have hsin : Real.sin β = Real.sin α :=
    Real.sin_periodic.sub_zsmul_eq (toIcoDiv hp 0 α)
  have hdir : direction (e₁ x) (e₂ x) β = direction (e₁ x) (e₂ x) α := by
    simp only [direction, hcos, hsin]
  have hh := hb (x, β) ⟨hx, hβ⟩
  change c ≤ normalSize (X x) (Y x) (C x) (R x • direction (e₁ x) (e₂ x) β) ∧
    normalSize (X x) (Y x) (C x) (R x • direction (e₁ x) (e₂ x) β) ≤ D ∧
    1 / normalSize (X x) (Y x) (C x) (R x • direction (e₁ x) (e₂ x) β) ≤ 1 / c at hh
  rwa [hdir] at hh

end ClosedSurfaceR4.VelocityFrame

end

end OAI
